#!/usr/bin/perl

# Arrays of intro, body, and closing content
@intro = ('Speclet_010_Intro.html');
@content = (
  'Speclet_020_IDB_API_Constructs.html',
  'Speclet_023_IDB_API_Asynchronous_APIs.html',
# Synchronous API deferred from V1
#  'Speclet_022_IDB_API_Synchronous_APIs.html',
  'Speclet_021_IDB_API_Algorithms.html'
);
@ending = ('Speclet_030_Privacy_Authorization.html');

# Load tempate and content
$template = loadContent('template.html');
$intro = concatContent(@intro);
$body = concatContent(@content);
$ending = concatContent(@ending);

# Replace markers in template
$template =~ s/<!-- intro-content -->/$intro/;
$template =~ s/<!-- body-content -->/$body/;
$template =~ s/<!-- ending-content -->/$ending/;

# Print resulting file
print $template;


####################################################################
# Read complete file
sub loadContent {
  local($content);
  $content = "";
  open(CONTENT,$_[0]) || die "Couldn't open $_[0]\n";
  while(<CONTENT>) {
    $content .= $_;
  }
  close(CONTENT);
  $content;
}

####################################################################
# Read file and extract content between begin and end markers
sub getContent {
  open(CONTENT,$_[0]) || die "Couldn't open $_[0]\n";
  local($content,$incontent);
  $content = "";
  $incontent = 0;
  while(<CONTENT>) {
    if(/<!-- begin-content -->/) {
      $incontent = 1;
    } elsif(/<!-- end-content -->/) {
      $incontent = 0;
    } elsif($incontent) {
      $content .= $_;
    }
  }
  close(CONTENT);
  $content;
}

####################################################################
# Concatenate content from multiple files
sub concatContent {
  local($content);
  $content = "";
  foreach $item (@_) {
    $content .= getContent($item);
  }
  $content;
}
