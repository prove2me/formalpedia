-- Prove2me | Definitions.Def_CatalyticSorting494_Sorting_SortingInstance
-- name    : CatalyticSorting494_Sorting_SortingInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:17.785113+00:00
-- url     : https://prove2.me/theorems/8fe9d94e-8662-4a48-a2c2-db910b20790b
-- title:
--   Lists of b-bit numbers, their input encoding, and the encoding of the sorted list
-- statement:
--   An instance of sorting is a list $v_1,\dots,v_n$ of $n$ natural numbers with $v_i<2^b$; repetitions are allowed. The input tape holds the width $L=\lfloor\log_2(n+b)\rfloor+1$ in unary, then $n$ and $b$ in fields of $L$ bits, and then the $nb$ bits of the keys in order, each key least significant bit first.
--
--   The output is the sorted list: the unique nondecreasing rearrangement of $v_1,\dots,v_n$ with the same multiplicities, encoded as exactly $nb$ bits in the same format.
--
--   These are the input and output of Corollaries 1.3 and 3.3.
--
--   **Formalization Note** The sorted list is computed with Mathlib's insertion sort, which is used here only to name the list; it costs nothing inside any machine model.
-- source:
--   Adelmo Morrison Orozco, Nathan S. Sheffield, Ryan Williams, STOC 2027 submission #494 (October 2026), Corollary 3.3, printed p.12 (PDF p.13)

import Mathlib
import Definitions.Def_CatalyticSorting494_Sorting_Machine

namespace CatalyticSorting494.Sorting

/-- A list of `n` numbers of `b` bits each; repetitions are allowed. -/
def IsKeyList (n b : ℕ) (keys : List ℕ) : Prop :=
  keys.length = n ∧ ∀ v ∈ keys, v < 2 ^ b

/-- The content of the input tape: a field width `L` in unary, then `n` and `b` in binary fields of
width `L`, then the `n` keys, each as `b` bits, least significant first. -/
def encodeKeys (n b : ℕ) (keys : List ℕ) : List Bool :=
  let L := Nat.log 2 (n + b) + 1
  List.replicate L true ++ [false] ++ natBits L n ++ natBits L b ++ keys.flatMap (natBits b)

/-- The encoding of the sorted list: the keys in nondecreasing order with their multiplicities, each
as `b` bits, least significant first. This has exactly `n * b` bits. -/
def sortedOutput (b : ℕ) (keys : List ℕ) : List Bool :=
  (keys.insertionSort (· ≤ ·)).flatMap (natBits b)

end CatalyticSorting494.Sorting


