------------------------------ MODULE transaction_lifecycle ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Stores, Connections, Transactions, Versions, MaxRequests
VARIABLES transactions, stores, pending_stores, connections, db_version, old_db_version, connection_queue, next_tx_order
\* TLA+ model of the transaction lifecycle and scheduling rules from:
\* - <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\* - <https://w3c.github.io/IndexedDB/#transaction-scheduling>

\* Note: by using only a singular `stores` and `db_version` variables,
\* we do not model multiple databases. 
Vars == << transactions, stores, pending_stores, connections, db_version, old_db_version, connection_queue, next_tx_order >>

Modes == {"readonly", "readwrite", "versionchange"}
TxStates == {"None", "Active", "Inactive", "Committing", "Finished"}

IsCreated(tx) == transactions[tx].state # "None"

Live(tx) == IsCreated(tx) /\ transactions[tx].state # "Finished"

Overlaps(tx1, tx2) == (transactions[tx1].stores \cap transactions[tx2].stores) # {}

\* Transactions are ordered by their creation time.
CreatedBefore(tx1, tx2) == transactions[tx1].creation_time < transactions[tx2].creation_time

\* Note: this is a model checker optimization only.
Symmetry == Permutations(Stores) \cup Permutations(Connections) \cup Permutations(Transactions)

ConnOpen(c) == connections[c].open

TxForConn(c) == { tx \in Transactions : Live(tx) /\ transactions[tx].conn = c }

AllTxFinishedForConn(c) ==
    \A tx \in Transactions:
        (transactions[tx].conn = c /\ IsCreated(tx)) => (transactions[tx].state = "Finished")

HasLiveUpgradeTx(c) ==
    \E tx \in Transactions:
        /\ Live(tx)
        /\ transactions[tx].conn = c
        /\ transactions[tx].mode = "versionchange"

\* <https://w3c.github.io/IndexedDB/#transaction-start>
CanStart(tx) ==
    LET m == transactions[tx].mode IN
        IF m = "readonly" THEN
            ~\E other \in (Transactions \ {tx}):
                /\ Live(other)
                /\ transactions[other].mode = "readwrite"
                /\ CreatedBefore(other, tx)
                /\ Overlaps(other, tx)
        ELSE IF m = "readwrite" THEN
            ~\E other \in (Transactions \ {tx}):
                /\ Live(other)
                /\ CreatedBefore(other, tx)
                /\ Overlaps(other, tx)
        ELSE \* versionchange transactions can always start.
            TRUE

-----------------------------------------------------------------------------------------
\* Invariants of the spec below.

\* Type invariant.
TypeOK ==
    /\ stores \in [Stores -> BOOLEAN]
    /\ pending_stores \in [Stores -> BOOLEAN]
    /\ db_version \in Versions
    /\ old_db_version \in Versions
    /\ connections \in [Connections ->
        [open: BOOLEAN,
         requested_version: Versions,
         closed: BOOLEAN,
         close_pending: BOOLEAN ]]
    /\ connection_queue \in Seq(Connections)
    /\ next_tx_order \in Nat
    /\ transactions \in [Transactions ->
        [conn: Connections,
         mode: Modes,
         stores: SUBSET Stores,
         requests  : Nat,
         processed_requests: Nat,
         handled_requests: Nat,
         state: TxStates,
         creation_time: Nat ]]

\* Safety property: A versionchange transaction being live excludes any other live transaction.
UpgradeTxExcludesOtherLiveTxs ==
    \A tx1 \in Transactions:
        (Live(tx1) /\ transactions[tx1].mode = "versionchange")
            => \A tx2 \in Transactions: Live(tx2) => (tx1 = tx2)

\* Inductive invariant that implies UpgradeTxExcludesOtherLiveTxs.
\*
\* If a versionchange transaction is live, then:
\* 1. Its connection is open and is at the head of the connection queue.
\* 2. All other connections are closed.
ActiveUpgradeTxImpliesExclusiveConn ==
    \A tx \in Transactions:
        (Live(tx) /\ transactions[tx].mode = "versionchange")
            =>
                /\ ConnOpen(transactions[tx].conn)
                /\ Len(connection_queue) > 0
                /\ Head(connection_queue) = transactions[tx].conn
                /\ \A c \in Connections: ConnOpen(c) => c = transactions[tx].conn

\* Invariant: A live transaction implies that the version of the connection is that of the db.
ActiveTransactionImpliesCorrectVersion ==
    \A tx \in Transactions:
        Live(tx) =>
            \/ (connections[transactions[tx].conn].requested_version = db_version)

\* Invariant: If a transaction has processed requests, it must have been able to start.
ProcessedRequestsImpliesStarted ==
    \A tx \in Transactions:
        (transactions[tx].processed_requests > 0) => CanStart(tx)

\* Invariant: If two transactions who are not the same are live, have started (processed requests),
\* and have overlapping scopes, then they must be read-only.
OverlappingStartedTxsAreReadOnly ==
    \A tx1, tx2 \in Transactions:
        (tx1 # tx2 
         /\ Live(tx1) /\ transactions[tx1].processed_requests > 0
         /\ Live(tx2) /\ transactions[tx2].processed_requests > 0
         /\ Overlaps(tx1, tx2))
            => (transactions[tx1].mode = "readonly" /\ transactions[tx2].mode = "readonly")
-----------------------------------------------------------------------------------------

DefaultTx ==
    [ conn     |-> CHOOSE c \in Connections : TRUE,
        mode      |-> "readonly",
        stores    |-> {},
        requests  |-> 0,
        processed_requests |-> 0,
        handled_requests |-> 0,
        state     |-> "None",
        creation_time |-> 0 ]

DefaultConn ==
    [ open            |-> FALSE,
        requested_version|-> 0,
        closed          |-> FALSE,
        close_pending   |-> FALSE ]

Init ==
    /\ transactions = [tx \in Transactions |-> DefaultTx]
    /\ stores = [s \in Stores |-> FALSE]
    /\ pending_stores = [s \in Stores |-> FALSE]
    /\ connections = [c \in Connections |-> DefaultConn]
    /\ db_version = 0
    /\ old_db_version = 0
    /\ connection_queue = <<>>
    /\ next_tx_order = 0

\* <https://w3c.github.io/IndexedDB/#open-a-database-connection>
StartOpenConnection(c, requested_version) ==
    \* Note: each connection can be opened only once,
    \* in order to reduce the state space.
    /\ connections[c] = DefaultConn
    /\ Len(connection_queue) < Cardinality(Connections)
    /\ connections' = [connections EXCEPT
            ![c] = [open            |-> FALSE,
                    requested_version|-> requested_version,
                    closed          |-> FALSE,
                    close_pending   |-> FALSE]
        ]
    /\ connection_queue' = Append(connection_queue, c)
    /\ UNCHANGED <<transactions, stores, pending_stores, db_version, old_db_version, next_tx_order>>

\* <https://w3c.github.io/IndexedDB/#open-a-database-connection>
FinishOpenConnection(c) ==
    /\ Len(connection_queue) > 0
    \* Wait until all previous requests in queue have been processed.
    /\ c = Head(connection_queue)
    /\ (connections[c].requested_version = db_version \/ connections[c].closed)
	\* <https://w3c.github.io/IndexedDB/#upgrade-a-database>
	\* Wait for transaction to finish.
    /\ ~HasLiveUpgradeTx(c)
    /\ IF connections[c].closed
       \* If connection was closed, 
       \* return a newly created "AbortError" DOMException and abort these steps.
       THEN connections' = connections
       ELSE connections' = [connections EXCEPT ![c].open = TRUE]
    /\ connection_queue' = Tail(connection_queue)
    /\ UNCHANGED <<transactions, stores, pending_stores, db_version, old_db_version, next_tx_order>>

\* <https://w3c.github.io/IndexedDB/#open-a-database-connection>
RejectOpenConnection(c) ==
    /\ Len(connection_queue) > 0
    \* Wait until all previous requests in queue have been processed.
    /\ c = Head(connection_queue)
    \* If db’s version is greater than version, 
    \* abort these steps.
    /\ connections[c].requested_version < db_version
    /\ connections' = [connections EXCEPT ![c] = DefaultConn]
    /\ connection_queue' = Tail(connection_queue)
    /\ UNCHANGED <<transactions, stores, pending_stores, db_version, old_db_version, next_tx_order>>

\* <https://w3c.github.io/IndexedDB/#open-a-database-connection>
CreateUpgradeTransaction(c) ==
    LET 
	    freeTxs == { t \in Transactions : ~IsCreated(t) }
		tx == CHOOSE t \in freeTxs : TRUE
	IN
    /\ Len(connection_queue) > 0
	/\ ~ConnOpen(c)
    \* Wait until all previous requests in queue have been processed.
    /\ c = Head(connection_queue)
    /\ connections[c].requested_version > db_version
    \* Wait until all connections in openConnections are closed.
    /\ \A other \in (Connections \ {c}): ~ConnOpen(other)
    /\ freeTxs # {}
    \* Run upgrade a database using connection, version and request.
    /\ transactions' = [transactions EXCEPT
                ![tx] = [conn     |-> c,
                        mode      |-> "versionchange",
                        stores    |-> { s \in Stores : stores[s] },
                        requests  |-> 0,
                        processed_requests |-> 0,
                        handled_requests |-> 0,
                        state     |-> "Active",
                        creation_time |-> next_tx_order]
            ]
    /\ connections' = [connections EXCEPT
                ![c].open = TRUE
            ]
    /\ pending_stores' = stores
    /\ old_db_version' = db_version
    /\ db_version' = connections[c].requested_version
    /\ next_tx_order' = next_tx_order + 1
    /\ UNCHANGED <<stores, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#close-a-database-connection>
StartCloseConnection(c, forced) ==
    /\ ConnOpen(c)
    /\ ~connections[c].close_pending
    /\ IF forced /\ HasLiveUpgradeTx(c)
       THEN connections' = [connections EXCEPT ![c].close_pending = TRUE, ![c].requested_version = old_db_version]
       ELSE connections' = [connections EXCEPT ![c].close_pending = TRUE]
    /\ IF forced
       THEN 
            \* https://w3c.github.io/IndexedDB/#abort-a-transaction
            /\ transactions' = [tx \in Transactions |->
                IF transactions[tx].conn = c /\ transactions[tx].state \notin {"None", "Finished"}
                THEN [transactions[tx] EXCEPT !.state = "Finished"]
                ELSE transactions[tx]]
            /\ IF HasLiveUpgradeTx(c)
            \* https://w3c.github.io/IndexedDB/#abort-an-upgrade-transaction
               THEN 
                    /\ pending_stores' = stores
                    /\ db_version' = old_db_version
                    /\ UNCHANGED <<stores, old_db_version>>
               ELSE 
                    /\ UNCHANGED <<stores, pending_stores, db_version, old_db_version>>
       ELSE 
            /\ UNCHANGED <<transactions, stores, pending_stores, db_version, old_db_version>>
    /\ UNCHANGED <<connection_queue, next_tx_order>>

\* <https://w3c.github.io/IndexedDB/#close-a-database-connection>
FinishCloseConnection(c) ==
    /\ connections[c].close_pending
    \* "Wait for all transactions created using connection to complete.
    \* Once they are complete, connection is closed."
    /\ AllTxFinishedForConn(c)
    /\ connections' = [connections EXCEPT 
            ![c].open = FALSE,
            ![c].closed = TRUE]
    /\ transactions' = [tx \in Transactions |-> 
            IF transactions[tx].conn = c 
            THEN DefaultTx 
            ELSE transactions[tx]]
    /\ UNCHANGED <<stores, pending_stores, db_version, old_db_version, connection_queue, next_tx_order>>

\* <https://w3c.github.io/IndexedDB/#dom-idbdatabase-transaction>
CreateTransaction(c, mode, scope) ==
    LET freeTxs == { t \in Transactions : ~IsCreated(t) } IN
    /\ freeTxs # {}
    /\ ConnOpen(c)
    \* If this’s close pending flag is true, then throw.
    /\ ~connections[c].close_pending
    \* If a live upgrade transaction is associated with the connection, throw.
    /\ ~HasLiveUpgradeTx(c)
    /\ \A s \in scope: stores[s]
    /\ LET tx == CHOOSE t \in freeTxs : TRUE IN
       /\ transactions' = [transactions EXCEPT
                ![tx] = [conn     |-> c,
                        mode      |-> mode,
                            stores    |-> scope,
                                requests  |-> 0,
                                processed_requests |-> 0,
                                handled_requests |-> 0,
                                state     |-> "Active",
                                creation_time |-> next_tx_order]
            ]
    /\ next_tx_order' = next_tx_order + 1
    /\ UNCHANGED <<stores, pending_stores, connections, db_version, old_db_version, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#asynchronously-execute-a-request>
ProcessRequest(tx) ==
    /\ CanStart(tx)
    /\ ConnOpen(transactions[tx].conn)
    /\ transactions[tx].state \in {"Active", "Inactive"}
    /\ transactions[tx].processed_requests < transactions[tx].requests
    \* Set request’s processed flag to true.
    /\ transactions' = [transactions EXCEPT
                ![tx].processed_requests = @ + 1,
                ![tx].state = "Active"
            ]
    /\ UNCHANGED <<stores, pending_stores, connections, db_version, old_db_version, connection_queue, next_tx_order>>

\* <https://w3c.github.io/IndexedDB/#asynchronously-execute-a-request>
AddRequest(tx) ==
    \* Assert: transaction’s state is active.
    /\ transactions[tx].state = "Active"
    /\ transactions[tx].requests < MaxRequests
    /\ transactions' = [transactions EXCEPT ![tx].requests = @ + 1]
    /\ UNCHANGED <<stores, pending_stores, connections, db_version, old_db_version, connection_queue, next_tx_order>>


\* <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\*
\* "Once the event dispatch is complete, the transaction's state
\* is set to inactive again".
\*
\* Note: AddRequest and Deactivate modeled as two steps,
\* even though in practice this happens in the same event-loop task.
\* This does not change anything other than making for easier modelling of adding 
\* any number of requests while the transaction is active.
Deactivate(tx) ==
    /\ transactions[tx].state = "Active"
    /\ transactions[tx].handled_requests < transactions[tx].processed_requests
    /\ transactions' = [transactions EXCEPT 
            ![tx].state = "Inactive",
            ![tx].handled_requests = @ + 1]
    /\ UNCHANGED <<stores, pending_stores, connections, db_version, old_db_version, connection_queue, next_tx_order>>

\* <https://w3c.github.io/IndexedDB/#transaction-commit>
\* The implementation must attempt to commit an inactive transaction 
\* when all requests placed against the transaction have completed
\* and their returned results handled, 
\* no new requests have been placed against the transaction,
\* and the transaction has not been aborted
AutoCommit(tx) ==
    /\ transactions[tx].state = "Inactive"
    /\ transactions[tx].requests = transactions[tx].processed_requests
    /\ transactions[tx].requests = transactions[tx].handled_requests
    /\ transactions' = [transactions EXCEPT ![tx].state = "Committing"]
    /\ UNCHANGED <<stores, pending_stores, connections, db_version, old_db_version, connection_queue, next_tx_order>>

\* <https://w3c.github.io/IndexedDB/#commit-a-transaction>
Commit(tx) ==
    /\ transactions[tx].state \notin {"None", "Committing", "Finished"}
    /\ transactions' = [transactions EXCEPT ![tx].state = "Committing"]
    /\ UNCHANGED <<stores, pending_stores, connections, db_version, old_db_version, connection_queue, next_tx_order>>

\* <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\* "When a transaction is committed or aborted, its state is
\* set to finished".
\*
\* Note: The commit/abort logic is only applied to store operations (CreateStore/DeleteStore)
\* and the db version. We do not model data operations or their side effects/rollback, as it would
\* make the spec significantly more complicated without adding much value to the
\* transaction lifecycle concurrency model.
CommitDone(tx) ==
    /\ transactions[tx].state = "Committing"
    /\ transactions' = [transactions EXCEPT ![tx].state = "Finished"]
    /\ IF transactions[tx].mode = "versionchange"
            THEN
                /\ stores' = pending_stores
                /\ db_version' = connections[transactions[tx].conn].requested_version
                /\ UNCHANGED <<pending_stores, old_db_version>>
            ELSE
                /\ UNCHANGED <<stores, pending_stores, db_version, old_db_version>>
    /\ UNCHANGED <<connections, connection_queue, next_tx_order>>

\* <https://w3c.github.io/IndexedDB/#abort-a-transaction>
Abort(tx) ==
    /\ transactions[tx].state \notin {"None", "Finished"}
    /\ transactions' = [transactions EXCEPT ![tx].state = "Finished"]
    /\ IF transactions[tx].mode = "versionchange"
            THEN
                \* <https://w3c.github.io/IndexedDB/#abort-an-upgrade-transaction>
                /\ pending_stores' = stores
                /\ connections' = [connections EXCEPT ![transactions[tx].conn].requested_version = old_db_version]
                /\ db_version' = old_db_version
                /\ UNCHANGED <<stores, old_db_version>>
            ELSE
                /\ UNCHANGED <<stores, pending_stores, db_version, old_db_version, connections>>
    /\ UNCHANGED <<connection_queue, next_tx_order>>

\* <https://w3c.github.io/IndexedDB/#dom-idbdatabase-createobjectstore>
CreateStore(tx, s) ==
    /\ CanStart(tx)
    \* Let transaction be database’s upgrade transaction if it is not null, or throw. 
    /\ transactions[tx].mode = "versionchange"
    \* If transaction’s state is not active, then throw.
    /\ transactions[tx].state = "Active"
    /\ ~pending_stores[s]
    /\ pending_stores' = [pending_stores EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<transactions, stores, connections, db_version, old_db_version, connection_queue, next_tx_order>>

\* <https://w3c.github.io/IndexedDB/#dom-idbdatabase-deleteobjectstore>
DeleteStore(tx, s) ==
    /\ CanStart(tx)
    \* Let transaction be database’s upgrade transaction if it is not null, or throw. 
    /\ transactions[tx].mode = "versionchange"
    \* If transaction’s state is not active, then throw.
    /\ transactions[tx].state = "Active"
    /\ pending_stores[s]
    /\ pending_stores' = [pending_stores EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<transactions, stores, connections, db_version, old_db_version, connection_queue, next_tx_order>>

\* When all connections went through their open and close cyle: infinite stuttering.
\* This is a way to avoid deadlock while bounding the spec.
AllClosed ==
    /\ \A c \in Connections: connections[c].closed
    /\ UNCHANGED Vars

Next ==
    \/ \E c \in Connections, v \in Versions: StartOpenConnection(c, v)
    \/ \E c \in Connections: FinishOpenConnection(c)
    \/ \E c \in Connections: RejectOpenConnection(c)
    \/ \E c \in Connections, forced \in BOOLEAN: StartCloseConnection(c, forced)
    \/ \E c \in Connections: FinishCloseConnection(c)
    \/ \E c \in Connections: CreateUpgradeTransaction(c)
    \/ \E c \in Connections, m \in {"readonly", "readwrite"}, scope \in SUBSET Stores:
            CreateTransaction(c, m, scope)
    \/ \E tx \in Transactions:
            (\/ AddRequest(tx)
             \/ ProcessRequest(tx)
             \/ Deactivate(tx)
             \/ AutoCommit(tx)
             \/ Commit(tx)
             \/ CommitDone(tx)
             \/ Abort(tx)
             \/ \E s \in Stores: \/ CreateStore(tx, s) 
                                 \/ DeleteStore(tx, s))
    \/ AllClosed

Spec == Init /\ [][Next]_Vars

====
