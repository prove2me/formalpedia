-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_UniqueWords
-- name    : DeletionHash_MixedEdit_UniqueWords
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:06.485667+00:00
-- url     : https://prove2.me/theorems/f003f9be-1c3c-471b-a9bf-15c035963e85
-- title:
--   Substring uniqueness and the large word family
-- statement:
--   A word is $j$-unique when its length-$j$ substrings at different valid starts are all different. Write $W_{n,k}$ for the finite family of $k$-unique words of length $n$, and set
--   $$k=2\lceil\log_q n\rceil+2.$$
--   All occurrences are indexed by their actual starts; a length exceeding the word length gives an empty window list and vacuous uniqueness. The natural ceiling agrees with the ordinary ceiling when $n\ge1$ and $q\ge2$. This family is a proof tool and does not restrict the channel or the final code-existence conclusion.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), §2.1, k, j-uniqueness and W_{n,k}, printed p. 5 (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Words
import Definitions.Def_DeletionHash_MixedEdit_Redundancy

namespace DeletionHash.MixedEdit

universe u

def IsUnique {α : Type u} (j : ℕ) (x : List α) : Prop := (windows j x).Nodup

noncomputable def uniqueLength (q n : ℕ) : ℕ := 2 * ⌈logBase q (n : ℝ)⌉₊ + 2

noncomputable def uniqueFamily (α : Type u) [Fintype α] (n k : ℕ) : Finset (Word α n) := by
  classical
  exact Finset.univ.filter (fun x => IsUnique k (letters x))

end DeletionHash.MixedEdit


