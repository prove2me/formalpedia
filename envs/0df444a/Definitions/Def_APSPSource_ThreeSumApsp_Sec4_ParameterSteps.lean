-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec4_ParameterSteps
-- name    : APSPSource_ThreeSumApsp_Sec4_ParameterSteps
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:27:48.093935+00:00
-- url     : https://prove2.me/theorems/2ad018b4-1cda-499b-bfe5-1536abe15c49
-- title:
--   Dimensions, switching order, and the parameter inequality
-- statement:
--   The size record contains the original inner dimension $D_0$, the outer dimension $N$, and the exponent $m$ of the padded dimension $D=4^m$. Its setup condition is $D_0\ge2$ and $m=\lceil\log_4D_0\rceil$.
--
--   For a real switching fraction $\theta$, define $t=\lceil\theta m\rceil_\mathbb N$, where the natural-valued ceiling is zero for negative inputs. The parameter expression on the left of Equation (10) is
--
--   $$H(L,m,\gamma)=\frac{(4^m)^\gamma10^L}{\sqrt{\binom Lm}\,3^{L-m}}.$$
--
--   These definitions record the sizes and expressions used when choosing parameters in Section 4.4. The desired inequality $H(L,m,\gamma)\le N$ is proved separately.
--
--   References:
--
--   1. [Source formalization, lines 71–83](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/ParameterSteps.lean#L71-L83).
--   2. [Source formalization, lines 137–139](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/ParameterSteps.lean#L137-L139).
--   3. [Source formalization, lines 189–191](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/ParameterSteps.lean#L189-L191).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/ParameterSteps.lean#L71-L83; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/ParameterSteps.lean#L137-L139; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/ParameterSteps.lean#L189-L191

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Theorem30
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
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
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
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
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
# Section 4.4: the steps of the proof of Corollary 26 that hold for all parameters

The proof of Corollary 31 begins: "We repeat the proof of Corollary 26 with L := ⌈cm⌉ and t :=
⌈θm⌉". This file has the parts of the proof of Corollary 26 that mention neither `L = 21m` nor
`t = ⌈m/9⌉`, under the headings of that proof. Both corollaries use them.

* Setting up. The inner dimension is padded to `D = 4^m` with `m = ⌈log_4 D⌉`
  (`Corollary26.setting_up`). This changes no entry of the product (`Corollary26.padding`), and it
  changes the bounds by a constant factor (`padded_le`). The switching order `t = ⌈θm⌉` is
  `switchOf θ m`, and `t ≤ m` (`switchOf_le`).
* Queries. `∑_{d ≤ t} α_d ≤ (9x)^t (1 + 1/x)^m` for every `x ≥ 1/9` (`sum_alpha_le`), and for
  `x = (1-θ)/θ` the right-hand side at `t = θm` is `D^q` (`rpow_mul_pow_eq_D_rpow_qOf`).
* Encodings. Inequality (10), whose left-hand side is `lhs10 L m γ`, bounds the last term of (8) and
  gives the hypothesis `N ≥ √K N₀` of Theorem 30 (`Equation10.last_term`, `Equation10.tile_fits`).
* Conclusion. The expression (8) from a bound on its first term and (10)
  (`dominated_cost8_of_eq_10`).

Bounds "up to a constant" are written with `Dominated`, in the one parameter `m` or in the record
`Sizes` of the given inner dimension, of `N` and of `m`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Setting up -/






























/-- The numbers in which the bounds of Section 4.4 are stated. -/
structure Sizes where
  /-- The given inner dimension, before the padding. -/
  D₀ : ℕ
  /-- The size of the product: the matrices are `N × D₀` and `D₀ × N`. -/
  N : ℕ
  /-- The padded inner dimension is `D = 4^m`. -/
  m : ℕ

/-- Proof of Corollary 26, "Setting up": "m := ⌈log_4 D⌉", for a given inner dimension `D₀ ≥ 2`. -/
structure Sizes.SetUp (p : Sizes) : Prop where
  two_le : 2 ≤ p.D₀
  m_eq : p.m = ⌈Real.logb 4 (p.D₀ : ℝ)⌉₊





















































/-- The switching order `t = ⌈θm⌉`: "t := ⌈m/9⌉" in the proof of Corollary 26, where `θ = 1/9`, and
"t := ⌈θm⌉" in the proof of Corollary 31. -/
noncomputable def switchOf (θ : ℝ) (m : ℕ) : ℕ := ⌈θ * (m : ℝ)⌉₊





/-! ### Queries -/









































/-! ### Encodings -/

/-- The left-hand side of (10): "D^γ · 10^L / (√K N₀)", with `D = 4^m`. Inequality (10) says that it
is at most `N`. -/
noncomputable def lhs10 (L m : ℕ) (γ : ℝ) : ℝ := (D m : ℝ) ^ γ * (10 : ℝ) ^ L / sqrtKN0 L m


























/-! ### Conclusion -/























end ThreeSumApsp


