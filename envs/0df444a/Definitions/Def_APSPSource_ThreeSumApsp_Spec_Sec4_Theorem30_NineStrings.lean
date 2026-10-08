-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_NineStrings
-- name    : APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_NineStrings
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:36:24.124708+00:00
-- url     : https://prove2.me/theorems/683df8de-b80f-41f8-b898-a3704ccce374
-- title:
--   Enumerating decimal strings with a bounded number of nines
-- statement:
--   The recursive list $S(n,l,h)$ is intended to enumerate length-$n$ strings over $\{0,\ldots,9\}$ containing between $l$ and $h$ occurrences of $9$. Its defining recursion is
--
--   $$S(0,l,h)=\begin{cases}[[]],&l=0,\\[],&l>0,\end{cases}$$
--   $$S(n+1,l,h)=\mathop{\Vert}_{d=0}^{8}\bigl(d::S(n,l,h)\bigr)\ \Vert\ \begin{cases}[],&h=0,\\9::S(n,l\mathbin{\dot-}1,h-1),&h>0.\end{cases}$$
--
--   Here prefixing a digit acts on every string of a list, $\Vert$ denotes list concatenation, and $\dot-$ is subtraction truncated at zero.
--
--   For admissible bounds $l\le\min\{h,n\}$, the proposed starting string consists of $n-l$ zeros followed by $l$ nines. Further functions attempt to raise a digit, find a successor, and iterate that successor while retaining the current string if no successor exists. Auxiliary predicates describe successive list entries and blocks sharing their first digit.
--
--   These are the enumeration data for boxes and leaves in the query construction. Ordering, exact coverage, and agreement between successor iteration and the recursive list are separate results.
--
--   References:
--
--   1. [Source formalization, lines 47–75](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/NineStrings.lean#L47-L75).
--   2. [Source formalization, lines 275–278](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/NineStrings.lean#L275-L278).
--   3. [Source formalization, lines 314–318](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/NineStrings.lean#L314-L318).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/NineStrings.lean#L47-L75; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/NineStrings.lean#L275-L278; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec4/Theorem30/NineStrings.lean#L314-L318

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Strings of digits with a bounded number of nines (Section 4.2, proofs of Lemma 29, Theorem 30)

All three enumerations of Section 4 come from one: `nineStrs n lo hi`, the strings of n digits
0, …, 9 in which the digit 9 (the digit of P₀) occurs at least lo and at most hi times, in
lexicographic order.

* The boxes with e stars are the leaves with between e and m - t symbols P₀, with their e lowest
  symbols P₀ turned into stars (the proof of Lemma 29).
* The leaves of order below t contributing to an output string η (the paper's w) have, at the m
  levels of its inner set Q, a string with at least m - t + 1 nines (proof of Theorem 30).
* The boxes of η have, at the m levels of Q, a string with exactly m - t nines, the nines being the
  levels of V (Section 4.2).

The file proves what the list contains (`mem_nineStrs`), that it is increasing
(`pairwise_lt_nineStrs`), how long it is (`length_nineStrs`: ∑_f binom(n, f) 9^{n-f}), and how a
routine goes through it: it starts with `nineFirst` (`head?_nineStrs`), and `nineNext` goes from
each string to the next (`nineNext_getElem`); so the string reached after i steps,
`nineStr n lo hi i`, is the member number i (`getElem_nineStrs`).  Read from the right end of the
string, `nineNext` is one pass: skip the positions that cannot be raised, raise one digit
(`nineRaise`), and fill the rest with the least admissible string, zeros followed by nines.  The
proof follows the recursion of the list: the strings with the first digit d form a block,
`nineNext` goes through each block (`nextTo_map_cons`), and from the last string of a block to the
first string of the next block (`head_nineBlocks`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- The strings of n digits below 10 with between lo and hi digits 9, in lexicographic order. -/
def nineStrs : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, lo, _ => if lo = 0 then [[]] else []
  | n + 1, lo, hi =>
    (List.range 9).flatMap (fun d => (nineStrs n lo hi).map (d :: ·)) ++
      (if hi = 0 then [] else (nineStrs n (lo - 1) (hi - 1)).map (9 :: ·))

/-- The least string of n digits with at least lo digits 9: zeros, then lo nines. -/
def nineFirst (n lo : ℕ) : List ℕ := List.replicate (n - lo) 0 ++ List.replicate lo 9

/-- The first digit d raised by one, if that is possible, and the least admissible string of n
digits behind it. -/
def nineRaise (lo hi n d : ℕ) : Option (List ℕ) :=
  if d < 8 then some ((d + 1) :: nineFirst n lo)
  else if d = 8 ∧ 0 < hi then some (9 :: nineFirst n (lo - 1))
  else none

/-- The string after l, or none if l is the last one: the rest of the string goes to the string
after it, or, if it is the last one, the first digit is raised. -/
def nineNext : ℕ → ℕ → List ℕ → Option (List ℕ)
  | _, _, [] => none
  | lo, hi, d :: l =>
    match nineNext (if d = 9 then lo - 1 else lo) (if d = 9 then hi - 1 else hi) l with
    | some l' => some (d :: l')
    | none => nineRaise lo hi l.length d

/-- The string number i of the list, as a routine reaches it: from the first string by going to the
next one i times. -/
def nineStr (n lo hi i : ℕ) : List ℕ := (fun l => (nineNext lo hi l).getD l)^[i] (nineFirst n lo)

/-! ## The members of the list -/

















































































/-! ## The length of the list -/







































































/-! ## The first string -/









































/-! ## From each string to the next -/

/-- f takes each member of the list to the following one, and the last one to z. -/
 def NextTo {α : Type} (f : α → Option α) : List α → Option α → Prop
  | [], _ => True
  | x :: r, z => f x = r.head?.or z ∧ NextTo f r z



































/-- The blocks of the strings with the first digits a, a + 1, …, a + k - 1, followed by the block
with the first digit 9: the end of the list `nineStrs (n + 1) lo hi`. -/
 def nineBlocks (n lo hi a k : ℕ) : List (List ℕ) :=
  (List.range' a k).flatMap (fun d => (nineStrs n lo hi).map (d :: ·)) ++
    (if hi = 0 then [] else (nineStrs n (lo - 1) (hi - 1)).map (9 :: ·))

section

variable {n lo hi : ℕ}












































end
























section

variable {n lo hi i : ℕ}































end

end ThreeSumApsp.Spec


