-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Lemma27_28
-- name    : APSPSource_ThreeSumApsp_Sec4_Lemma27_28
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:09:19.922281+00:00
-- url     : https://prove2.me/theorems/6be0ab9d-b204-46ac-b0d4-e1003063d00d
-- title:
--   Level sets and the box associated with a contributing leaf
-- statement:
--   Let $\eta$ be an output string of length $L$, let $Q$ be its inner-level set, and let $\tau$ be a leaf. Define
--
--   $$Z(Q,\tau)=\{\ell\in Q:\tau_\ell=P_0\}.$$
--
--   For a level subset $V$, the allowed-symbol set at a level follows four conditions: levels in $F_V$ carry a star; levels in $V\setminus F_V$ carry $P_0$; levels in $Q\setminus V$ carry one of the nine ordinary terms $P_{ij}$; levels outside $Q$ carry the term of $\eta$'s private leaf. Here $F_V$ consists of levels in $Q$ below every level of $Q\setminus V$.
--
--   Using the source's padded set $V(m,t,Q,Z)$, the associated cube is defined by
--
--   $$\operatorname{box}(m,t,\eta,\tau)=\operatorname{starAt}\!\left(F_{V(m,t,Q,Z(Q,\tau))},\tau\right).$$
--
--   That is, it keeps the leaf's symbols except for stars at the specified low levels. The function is total; the hypotheses that make this cube a box of a contributing leaf of sufficiently large order occur in later theorems.
--
--   These objects support the decomposition of a query into low-order leaves and box values.
--
--   References:
--
--   1. [Source formalization, lines 48–50](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Lemma27_28.lean#L48-L50).
--   2. [Source formalization, lines 230–236](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Lemma27_28.lean#L230-L236).
--   3. [Source formalization, lines 311–315](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Lemma27_28.lean#L311-L315).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Lemma27_28.lean#L48-L50; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Lemma27_28.lean#L230-L236; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Lemma27_28.lean#L311-L315

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Boxes
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Lemmas 27 and 28: the boxes of an output string (Section 4.2)

Let `η` be an output string (the paper's w) with inner set `Q` of `m` levels. A leaf `τ`
contributing to `η` chooses `P₀` at the set `Z` of levels of `Q`; `V` is `Z` padded from the bottom
to `m - t` levels; `F_V` is the longest initial segment of `Q` contained in `V`; and `𝓑_V` is the
set of the cubes with stars at `F_V`, with `P₀` at `V ∖ F_V`, with one of the nine terms `P_ij` at
each level of `Q ∖ V`, and with the terms of the private leaf of `η` outside `Q`. The file follows
the paper's order, except that Figure 10 comes after the definitions that it illustrates.

* *The sets `Z`, `V`, `F_V`.* The set `V` has `m - t` levels (`card_Vof`). The definition of `F_V`
  is the printed one (`FV_eq`). The condition `V ∖ F_V ⊆ Z` says that every level of `V ∖ Z` is
  below every level of `Q ∖ V` (`sdiff_FV_subset_iff`); this carries Lemma 27.
* *The sets `𝓑_V`.* They have `9^t` cubes (`card_BV`), which are boxes (`BV_isBox`), and they are
  disjoint (`BV_pairwiseDisjoint`). The box of a leaf is in `𝓑_V` for the `V` of the leaf
  (`boxOfLeaf_mem_BV`). A leaf contributing to `η` is a leaf of a box of `𝓑_V` if and only if
  `V ∖ F_V ⊆ Z ⊆ V` (`exists_mem_BV_leaf_iff`), and then of exactly one (`BV_leaf_unique`).
* *Figure 10*, for `m = 4` and `t = 2` (`figure_10_counts`, `figure_10_rows`, `figure_10_Vof`).
* **Lemma 27** (`lemma_27`): for `|Z| ≤ m - t`, the only `V` of `m - t` levels with
  `V ∖ F_V ⊆ Z ⊆ V` is `Z` padded from the bottom.
* **Lemma 28**: the leaves of order at least `t` contributing to `η` are the leaves of the boxes of
  the sets `𝓑_V` (`lemma_28_leaves`), and each of them lies in exactly one box (`lemma_28_unique`).
  So a sum over the leaves contributing to `η` splits into the leaves of order below `t` and the
  boxes (`Lemma28.sum_contributing`). For the products at the leaves this is the equation of the
  lemma (`lemma_28`), and for the constant 1 it counts the leaves (`Lemma28.card_leaves`). The
  numbers of terms are `∑_{d < t} α_d` and `α_t` (`lemma_28_counts`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L : ℕ}

/-! ### The sets `Z`, `V` and `F_V` (Section 4.2) -/

/-- Section 4.2: "Z := {ℓ ∈ Q : τ_ℓ = P₀} (the levels at which τ chooses P₀)". -/
def Zof (Q : Finset (Fin L)) (τ : Leaf L) : Finset (Fin L) :=
  Q.filter fun ℓ => τ ℓ = Term.P0




































































































/-! ### The sets `𝓑_V` (Section 4.2) -/

section BV

variable {η : OutStr L} {V : Finset (Fin L)} {π : Cube L} {ℓ : Fin L}








































































end BV

/-- The symbols allowed at level `ℓ` in a cube of `𝓑_V`. -/
 def allowed (η : OutStr L) (V : Finset (Fin L)) (ℓ : Fin L) : Finset CubeSymbol :=
  univ.filter fun s =>
    (ℓ ∈ FV (innerSetO η) V → s = CubeSymbol.star) ∧
    (ℓ ∈ V \ FV (innerSetO η) V → s = CubeSymbol.term Term.P0) ∧
    (ℓ ∈ innerSetO η \ V → ∃ i j, s = CubeSymbol.term (Term.P i j)) ∧
    (ℓ ∉ innerSetO η → s = CubeSymbol.term (privateLeaf η ℓ))










































































/-- Section 4.2: the box of a leaf `τ` of order at least `t` contributing to `η`: "The box of τ then
agrees with τ everywhere, except that it has a star at every level of Q below the level where we
stopped", these levels being those of `F_V` for the `V` of `τ`. -/
def boxOfLeaf (m t : ℕ) (η : OutStr L) (τ : Leaf L) : Cube L :=
  Cube.starAt (FV (innerSetO η) (Vof m t (innerSetO η) (Zof (innerSetO η) τ))) τ







































/-! ### Figure 10 -/
































/-! ### Lemma 27 -/





















/-! ### Lemma 28 -/



















































































































































end ThreeSumApsp


