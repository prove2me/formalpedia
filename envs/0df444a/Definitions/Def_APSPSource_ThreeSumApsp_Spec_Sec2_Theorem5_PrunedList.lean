-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_PrunedList
-- name    : APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_PrunedList
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:28:00.888976+00:00
-- url     : https://prove2.me/theorems/49a4997f-d6fb-4efb-8ead-d8541aa56928
-- title:
--   The pruned algebraic recursion on lists of requested codes
-- statement:
--   The list function $P(E_A,E_B,n,b,l)$ specifies the pruned computation for requested base-ten codes $l$, using two encoded arrays beginning at offset $b$. At depth zero it returns one copy of $E_A[b]E_B[b]$ for each requested code; missing array entries are read as zero.
--
--   At depth $n+1$, child $t\in\{0,\ldots,9\}$ receives the source's child list and offset $b+t10^n$. Empty child lists are skipped. The gather operation restricts each returned child list to its requested output slice. Slices with leading digit below nine use their corresponding child; the leading-nine slice sums the restricted contributions from all ten children.
--
--   This is the list-level recurrence for the `Pruned` procedure of Section 2.4.2.
--
--   References:
--
--   1. [Source formalization, lines 36–52](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/PrunedList.lean#L36-L52).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec2/Theorem5/PrunedList.lean#L36-L52

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_SortedSets
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The pruned recursion on lists

`Pruned` (Section 2.4.2) restated on increasing lists of codes: `prunedList`.  The two encodings are
two lists of `10^L` numbers, and a vertex `τ₁ ⋯ τ_k` is given by the position `base` at which its
part of the encodings begins, that is, by the code of `τ₁ ⋯ τ_k` times `10^{L-k}`.  The result is
the list of the values in the order of the list passed.

* **Correctness** (`prunedList_spec`, `prunedList_root`): by induction on the length `n = L - k` of
  the strings passed, as in the proof of Lemma 10.  A child returns the array `C_λ` of step (3) by
  the induction hypothesis.  Step (4), which puts the output together from restrictions of the
  `C_λ`, is a function of its own, `gather`, with its own lemma (`gather_spec`): the slice at `z_ij`
  comes from `C_{P_ij}`, and the slice at `z₀` is the sum of all ten `C_λ`.
* **Work** (`prunedWork_le`): `callSizes` follows the recursion of `prunedList` and lists the
  lengths of the lists passed to its calls.  These are the sizes of the sets passed to the calls of
  `Pruned` (`callSizes_spec`), and Lemma 10 bounds their total.  The work of a call is its own plus
  that of the children that are called (`prunedWork_succ`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The function -/

/-- Step (4) of `Pruned` on lists.  `l` is the list passed to the call, its strings have length
`n + 1`, and `C t` is the list that the child with digit `t` has returned.  The segment of the
output with first digit `t < 9` (the slice at `z_ij`) is the restriction of `C t`, and the segment
with first digit 9 (the slice at `z₀`) is the sum of the restrictions of all ten `C t`. -/
def gather (n : ℕ) (l : List ℕ) (C : ℕ → List ℤ) : List ℤ :=
  (List.range 9).flatMap (fun t => restrictList (childList n t l) (C t) (sliceList n t l))
    ++ sumLists (sliceList n 9 l).length
      ((List.range 10).map fun t => restrictList (childList n t l) (C t) (sliceList n 9 l))

/-- `Pruned` on lists, steps (1) to (4) of Section 2.4.2: `prunedList EA EB n base l` is the call
that is passed the list `l` of codes of strings of length `n`, at the vertex whose part of the
encodings `EA` and `EB` begins at the position `base`.  A child whose list is empty is not called.
-/
def prunedList (EA EB : List ℤ) : ℕ → ℕ → List ℕ → List ℤ
  | 0, base, l => l.map fun _ => EA.getD base 0 * EB.getD base 0
  | n + 1, base, l => gather n l fun t =>
    if childList n t l = [] then [] else prunedList EA EB n (base + t * 10 ^ n) (childList n t l)

/-! ## The ten terms, in the order of their digits -/











































/-! ## Step (4): the output from the arrays of the children -/





















































/-! ## Correctness -/




















































/-! ## The calls and their work -/















































































end ThreeSumApsp.Spec


