-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_RepeatedSquaring
-- name    : APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_RepeatedSquaring
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:28:31.008068+00:00
-- url     : https://prove2.me/theorems/3b0daf50-e7a9-4f24-a621-a460812f7532
-- title:
--   Finite-sentinel lists for repeated min-plus squaring
-- statement:
--   A list encodes a matrix over $\mathbb Z\cup\{+\infty\}$ when its row-major entry equals the integer matrix entry, or a chosen sentinel $\mathrm{INF}$ for $+\infty$. A clipping function replaces every integer greater than a threshold by that sentinel.
--
--   The initial graph list puts zero on the diagonal, the supplied edge weight where an adjacency entry is one, and $\mathrm{INF}$ elsewhere. The squaring sequence uses $\mathrm{INF}=3nU$ and
--
--   $$L_{t+1}=\operatorname{clip}_{nU,3nU}(L_t\star L_t),$$
--
--   entrywise, where $\star$ is the integer min-plus product and $L_0$ is the initial graph list. These total functions specify the concrete arrays for the APSP reduction; their correctness follows under the graph and weight hypotheses in later proofs.
--
--   References:
--
--   1. [Source formalization, lines 36–42](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem21b/RepeatedSquaring.lean#L36-L42).
--   2. [Source formalization, lines 69–80](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem21b/RepeatedSquaring.lean#L69-L80).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem21b/RepeatedSquaring.lean#L36-L42; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem21b/RepeatedSquaring.lean#L69-L80

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Repeated squaring on lists of integers

For Theorem 21(b): if no closed walk has negative weight, then squaring the weight matrix `⌈log₂ n⌉`
times in the (min,+)-product yields the distance matrix, and all finite entries that occur have
absolute value at most `nU`, where `U` bounds the edge weights. The matrices of the repeated
squaring have entries that may be `+∞`, while a solver for the (min,+)-product works on integers.
Here `+∞` is written as the integer `3nU`.

* `squareList n U ADJ W t` is the list, row by row, after `t` rounds.  A round is a (min,+)-product
  of the list with itself, after which every entry above `nU` is set back to `3nU`.
* One round is right (`Encodes.square`): finite entries have absolute value at most `nU`, so a sum
  with an infinite term is at least `2nU`, and a finite sum is the sum of the two codes.
* By induction the list holds the matrix `minPlusSquares` of the repeated squaring, entry
  by entry (`encodes_squareList`), and after `⌈log₂ n⌉` rounds it holds the distances
  (`squareList_distances`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Entries that may be infinite, as integers -/

/-- The list `L` holds, row by row, the matrix `D`, with `INF` for `+∞`: the code `d.untopD INF` of
an entry `d` is the number itself, or `INF` if `d = +∞`. -/
def Encodes (n : ℕ) (INF : ℤ) (L : List ℤ) (D : Fin n → Fin n → WithTop ℤ) : Prop :=
  ∀ i j : Fin n, entry n L i j = (D i j).untopD INF

/-- Every number above `thr` becomes `INF`. -/
def clip (thr INF x : ℤ) : ℤ := if thr < x then INF else x
























/-! ## The lists of the repeated squaring -/

/-- The weight matrix of the graph (0 on the diagonal), row by row, with `INF` where there is no
edge. -/
def weightList (n : ℕ) (INF : ℤ) (ADJ W : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q =>
    if q / n = q % n then 0 else if ADJ.getD q 0 = 1 then W.getD q 0 else INF

/-- The matrix after `t` squarings, row by row, with `3nU` for `+∞`. -/
def squareList (n U : ℕ) (ADJ W : List ℤ) : ℕ → List ℤ
  | 0 => weightList n (3 * (n * U : ℕ)) ADJ W
  | t + 1 =>
    (minPlusList n (squareList n U ADJ W t) (squareList n U ADJ W t)).map
      (clip (n * U : ℕ) (3 * (n * U : ℕ)))









































































variable {n U : ℕ} {ADJ W : List ℤ}





















































end ThreeSumApsp.Spec


