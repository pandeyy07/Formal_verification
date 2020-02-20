///////////////////////////////////////////////////////////////
//1: isPrefix

predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) &&
	pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) ||
	pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{

	if(|pre| > |str|)
  {
    return false;
  }

	if(pre == str[0..|pre|])
	{
		return true;
	}
	else
	{
		return false;
	}
}

///////////////////////////////////////////////////////////////
//2: isSubstring

predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	res := false;

	if |sub| > |str| //substring cant be > than string
	{
		return res;
	}

	var lowerBound := 0;
	while(lowerBound <= |str|)
		invariant 0 <= lowerBound <= |str| + 1
		invariant !res <==> forall i ::( 0 <= i < lowerBound ==> isNotPrefixPred(sub, str[i..]))
		decreases |str| - lowerBound
	{
		var prefResult := isPrefix(sub, str[lowerBound..]);

		if prefResult == true
		{
			return true;
			break;
		}
		lowerBound := lowerBound + 1;
	}

	return res;
}

///////////////////////////////////////////////////////////////
//3: commonKSubstring

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	found := false;

	if |str1| < k || |str2| < k //substring of length k cant be greater than string
  {
    return found;
  }

	assert |str1| >= k && |str2| >= k;

	var lowerBound := 0;
	while((lowerBound + k) <= |str1|)
		invariant lowerBound <= |str1| - k + 1
		invariant !found <==> forall i, j :: (0 <= i < lowerBound && j == i + k  ==> isNotSubstringPred(str1[i..j], str2))
		decreases |str1| - lowerBound
	{
		var result := isSubstring(str1[lowerBound..lowerBound + k], str2);

		if result == true
	  {
	    found := true;
			break;
	  }

		lowerBound := lowerBound + 1;
	}

  return found;
}

///////////////////////////////////////////////////////////////
//4: maxCommonSubstringLength

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
	len := |str1|;

	while(len > 0)
		invariant forall i :: (len < i <= |str1| ==> !haveCommonKSubstringPred(i, str1, str2))
		decreases len
	{
		var kSubsRes := haveCommonKSubstring(len, str1, str2);
		if kSubsRes == true
		{
			return len;
		}
		len := len - 1;
	}
	
	assert isPrefixPred(str1[0..0], str2[0..]); //incase len becomes 0
	return len;

}


