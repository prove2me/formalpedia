-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Lemma10
-- name    : APSPSource_ThreeSumApsp_Sec2_Lemma10
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:47:09.914668+00:00
-- url     : https://prove2.me/theorems/42cf76b1-79eb-4de9-9530-99d06f280ae4
-- title:
--   Recursive computation of a leaf encoding
-- statement:
--   Let $A$ be a finite alphabet, let $\Lambda$ be the ten-term alphabet of the algebraic construction, and let $c:\Lambda\times A\to\mathbb Z$ be a coefficient function. For an integer array $a$ on length-$L$ strings and a leaf $\tau\in\Lambda^L$, define its recursive encoding by
--
--   $$E_c(0,a,\tau)=a[\varnothing],$$
--   $$E_c(L+1,a,\lambda\tau')=E_c\left(L,\ u'\mapsto\sum_{s\in A}c(\lambda,s)a[su'],\ \tau'\right).$$
--
--   The recursive step takes a coefficient-weighted sum of slices of $a$ and continues down the remaining leaf. Choosing the left or right coefficient family gives the two encoding procedures used in the algebraic algorithm.
--
--   This definition specifies the recursion. The theorem identifying its result with the closed leaf-encoding sum and bounds on its implementation are separate statements.
--
--   References:
--
--   1. [Source formalization, lines 44–52](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Lemma10.lean#L44-L52).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Lemma10.lean#L44-L52

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
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
# Sections 2.4.1 and 2.4.2: the encodings, the recursion `Pruned`, and Lemma 10

The encoding of an array is computed by `Full` with the other array left out (`computeEncoding_phi`,
`computeEncoding_psi`).  `Pruned(S)` is `Full` without that phase, and each call computes only the
outputs in the set `S` that is passed to it.  Lemma 10 (`lemma_10`) has three claims.

* Values.  One induction gives a closed form (`Pruned_eq_restrictTo_sum`): at a string of `S`,
  `Pruned` returns the sum, over the leaves contributing to the string, of the product of the two
  numbers looked up at the leaf.  With the encodings of `a` and `b` this sum is `Mult(a, b)` by
  definition (`Lemma10.values`), which is what `Full` returns by Lemma 7
  (`Pruned_eq_restrictTo_Full`).  The paper compares `Pruned` with `Full` level by level instead.
* Leaves visited.  A vertex below the root is called exactly if it contributes to a string of `U`
  (`Pruned.called_iff_root_or`, `Pruned.called_iff`; the step of the induction is
  `Pruned.called_succ`).  For leaves this is `Lemma10.leaves_visited`.  The set passed to a vertex
  consists of the suffixes of these strings (`Pruned.mem_passed_iff`; no later proof uses this).
* Total size.  A set of strings is no larger than its set of leaves, because a string is determined
  by its private leaf (`card_le_card_Leaves`), and the leaves of `Leaves(S)` that begin with
  `λ` are the leaves of `Leaves(S_λ)` with `λ` put in front (`card_Leaves_succ`).  So the
  sets passed at one depth have total size at most `|Leaves(U)|` (`Pruned.sum_card_passed_le`), and
  there are `L + 1` depths (`Lemma10.total_size`).

Which calls `Pruned` makes depends only on the set passed to it, so the second and the third claim
are proved for any two arrays in place of the two encodings.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Section 2.4.1: the encodings -/

/-- Section 2.4.1, the procedure that computes the encoding of `a`: "we run Full with b left out and
without step (4): […] the left number at the leaf τ is Φ_τ(a), and the leaf stores it." What is left
of `Full` is step (2) for `a`, the recursive calls of step (3), and at depth `L` the number that has
been reached. "The encoding of b […] is computed in the same way", so the procedure is written once,
for the coefficients `c` of any family of linear forms: `c = φ` for `a`, and `c = ψ` for `b`. -/
def computeEncoding {α : Type} [Fintype α] (c : Term → α → ℤ) :
    (L : ℕ) → ((Fin L → α) → ℤ) → Leaf L → ℤ
  | 0, a, _ => a Fin.elim0
  | L + 1, a, τ => computeEncoding c L (fun u' => ∑ s, c (τ 0) s * sliceAt a s u') (Fin.tail τ)
















/-! ### Section 2.4.2: the sets `S_λ` of step (2) -/





































/-! ### Lemma 10, first claim: the values -/
























































































/-! ### Lemma 10, second claim: the calls that are made and the sets passed to them -/




















































































































































































































































/-! ### Lemma 10, third claim: the total size of the sets passed -/





















































































































































end ThreeSumApsp


