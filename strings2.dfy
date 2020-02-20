predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || pre != str[..|pre|]
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

predicate isSubstringPred(sub:string, str:string)
{
  exists i, j :: 0 <= i <= j <= |str| && sub == str[i..j]
}

predicate isNotSubstringPred(sub:string, str:string)
{
	forall i, j :: 0 <= i <= j <= |str| ==> sub != str[i..j]
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
  exists a, b, c, d :: 0 <= a <= b <= |str1| && 0 <= c <= d <= |str2| && (b - a) == (d - c) == k && str1[a..b] == str2[c..d]
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall a, b, c, d :: 0 <= a <= b <= |str1| &&  0 <= c <= d <= |str2| ==> !((b - a) == (d - c) == k) || str1[a..b] != str2[c..d]
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==> haveNotCommonKSubstringPred(k,str1,str2)
{}
