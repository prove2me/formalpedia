-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Theorem30
-- name    : APSPSource_ThreeSumApsp_Sec4_Theorem30
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:09:23.072187+00:00
-- url     : https://prove2.me/theorems/3d42a034-2f27-422c-86f4-e086721689cf
-- title:
--   The query-value expression from encodings and box values
-- statement:
--   For natural parameters $L,m$, define the dimension scale
--
--   $$R(L,m)=\sqrt{\binom Lm}\,3^{L-m},$$
--
--   with natural subtraction in $L-m$. Let $A(\tau),B(\tau)$ be stored integer encodings for leaves $\tau$, let $\eta$ be an output string, and let $t$ be the order threshold. The specified query value is
--
--   $$Q_{m,t}(A,B,\eta)=\sum_{\tau\in\mathcal L_{<t}(\eta)}A(\tau)B(\tau)+\sum_{V\in\mathcal V_{m,t}(\eta)}\ \sum_{\pi\in\mathcal B_V(\eta)}\operatorname{DP}(A,B,|\operatorname{stars}(\pi)|,\pi).$$
--
--   Here $\mathcal L_{<t}(\eta)$ contains contributing leaves of order below $t$, $\mathcal V_{m,t}(\eta)$ contains subsets of the output's inner levels of size $m-t$, and $\mathcal B_V(\eta)$ is the associated family of boxes. The function $\operatorname{DP}$ is the previously defined recurrence for box values.
--
--   This expression states what a query adds from the encodings and stored box data. Equality with the desired matrix entry and the query's cost are separate correctness and complexity results.
--
--   References:
--
--   1. [Source formalization, lines 106–107](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Theorem30.lean#L106-L107).
--   2. [Source formalization, lines 369–377](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Theorem30.lean#L369-L377).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Theorem30.lean#L106-L107; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Theorem30.lean#L369-L377

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Equation (7) and Theorem 30: the data structure (Section 4.3)

The running times of Theorem 30 on the word RAM are `wordRam_theorem_30` and
`wordRam_theorem_30_wanted`; the expressions inside their `O(·)` are `cost8`, `cost9` and
`costQuery`. This file has the mathematics of the paper's proof, in the paper's order.

* *The decay rate.* `ρ = 9m/(L-m+1)` is less than 1 (`sec4_rho_lt_one`), the ratio `β_d/β_{d-1}` is
  at most `ρ` (`eq_7_ratio`), and so `β_d ≤ ρ^d M` (`eq_7`). This is equation (7).
* *Preprocessing: the count behind (8).* Here `sqrtKN0 L m` is `√K N₀`. Padding at most doubles `N`
  (`Theorem30.padding`; nothing else rests on this lemma). The list of subsets takes `K L ≤ 10^L`
  operations (`Theorem30.subsets`), which the last term of (8) absorbs
  (`Theorem30.subsets_absorbed`). There are at most `4N/(√K N₀)` bands (`Theorem30.bands`), with `N`
  the given size, by a slightly finer count than `K₀ ≥ √K/2` gives (`Theorem30.numBands_mul_le`);
  the input array of a band has at most `K N₀ D ≤ 7^L` nonzero entries
  (`Theorem30.K_mul_N0_mul_D_le`), and `L · 7^L ≤ 2 · 10^L` (`Theorem30.form_array`). There are at
  most `4N²/M` tiles (`Theorem30.tiles`) with at most `(m+1) ∑_{d ≥ t} β_d` boxes each (Lemma 29),
  and `∑_{d ≥ t} β_d ≤ M ρ^t/(1-ρ)` by (7) (`Theorem30.sum_beta`), which bounds the number of all
  boxes (`Theorem30.boxes_total`). The boxes (`Theorem30.boxes_cost`), the bands
  (`Theorem30.bands_cost`) and the list add up to at most a constant times the expression in (8)
  (`Theorem30.cost8_assembly`).
* *Query.* The sum of Lemma 28 for the output string of the position `(I, J)` is `(XY)[I, J]` by
  Section 2.4.4 (`Theorem30.query`). Each box of that sum is a box of the tile (`Theorem30.lookup`),
  and the dynamic program of Lemma 29 has stored its value (`dpValue_card_starLevels`); so the query
  returns `(XY)[I, J]` (`Theorem30.correct`). Expression (9) is `|W|` queries on top of (8)
  (`Theorem30.cost9_eq`).
* *Word size.* `10^L ≤ N^{5/2}` (`Theorem30.ten_pow_le`).

Here `N` is the given size throughout, and the padded size is `padN L m N`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### The decay rate `ρ` and equation (7) -/




















































/-! ### Theorem 30, "Preprocessing": the count behind (8) -/

/-- The number `√K N₀` of the hypothesis "N ≥ √K N₀" of Theorem 30 and of the last term of (8). -/
noncomputable def sqrtKN0 (L m : ℕ) : ℝ := Real.sqrt (K L m : ℝ) * (N0 L m : ℝ)







































































































































































































































/-! ### Theorem 30, "Query": a query returns `(XY)[I, J]` -/





























/-- A query, as in the proof of Theorem 30, for the output string `η` of the queried position,
reading only the two encodings of the tile and the stored values of its boxes: "for each such leaf τ
we look up its two numbers Φ_τ(a) and Ψ_τ(b) in the encodings of the tile and multiply them. The
second part is the sum of the values of the boxes of w: for every V ⊆ Q with |V| = m - t and every
box of 𝓑_V, we look up its value in the trie of the tile." The value stored for a box `π` with `e`
stars is the one that the dynamic program computed, `dpValue encA encB e π`. -/
def queryValue {L : ℕ} (m t : ℕ) (encA encB : Leaf L → ℤ) (η : OutStr L) : ℤ :=
  ∑ τ ∈ lowLeaves m t η, encA τ * encB τ
    + ∑ V ∈ Vsets m t η, ∑ π ∈ BV η V, dpValue encA encB (Cube.starLevels π).card π
























/-! ### Theorem 30, "Word size" -/















end ThreeSumApsp


