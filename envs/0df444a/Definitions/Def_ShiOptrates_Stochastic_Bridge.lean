-- Prove2me | Definitions.Def_ShiOptrates_Stochastic_Bridge
-- name    : ShiOptrates_Stochastic_Bridge
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-08T22:24:45.021473+00:00
-- url     : https://prove2.me/theorems/73818914-f93f-4412-a419-9b341b5c8760
-- title:
--   $\mathrm{innerBilin}$: the real inner product as a continuous bilinear map
-- statement:
--   A packaging device: the real inner product on $E$, presented as a continuous bilinear map $E\to E\to\mathbb{R}$ rather than as the bare function $\langle\cdot,\cdot\rangle$.
--
--   $$\mathrm{innerBilin}(x)(y)=\langle x,y\rangle_{\mathbb{R}}$$
--
--   The bilinear-map form is what allows the inner product to be pulled through a Bochner integral and a conditional expectation, which is the step connecting the martingale-difference orthogonality arguments to the deterministic recursion. Its defining simp lemma is included so that the packaging is transparent downstream.
-- source:
--   lean-optrates, https://github.com/shiy1022/lean-optrates/blob/4c0b84980914ea7f9007510d92bcd60e91ad8448/Optrates/Stochastic/Bridge.lean | Formalized by Yueheng Shi; Apache License 2.0. Platform copy produced by declaration-graph skeleton subtraction; root namespace `OptRates` renamed to `ShiOptRates`.

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/Bridge.lean
Original work Copyright (c) 2026 Yueheng Shi, released under the Apache License,
Version 2.0.  The original copyright and author notices are retained below.

MODIFICATIONS made for publication on Prove2me: declarations not reachable from
the published targets were removed by declaration-graph skeleton subtraction;
project imports were rewritten to platform `Definitions.Def_*` / `Theorems.Thm_*`
modules; the root namespace `OptRates` was renamed to `ShiOptRates`; 
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiOptrates_Cost
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_ShiOptrates_Stochastic_Recursion
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Martingale.Basic
/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# L3d — From a martingale difference to `L²` orthogonality

`Optrates.Stochastic.Accumulation` proves the `√K` accumulation law from an `L²`
orthogonality hypothesis, `∫ ⟪eₖ, ξₖ⟫ = 0`.  This file discharges that hypothesis from the
condition an actual stochastic algorithm satisfies: `ξₖ` is a martingale difference with
respect to a filtration to which `eₖ` is adapted.

This is the filtration layer the plan flagged as the likely sink.  It turns out to be
short, because Mathlib's `condExp_bilin_of_aestronglyMeasurable_left` already provides the
pull-out property for a general continuous bilinear map — so the vector-valued case needs
no more work than the scalar one, once the real inner product is packaged as such a map.

## Main definitions

* `innerBilin` — the real inner product as a continuous bilinear map, the form Mathlib's
  pull-out lemma consumes.

## Main results

* `integral_inner_eq_zero_of_condExp_eq_zero` — the tower-property step:
  `E[ξ | m] = 0` and `e` `m`-measurable give `E⟪e, ξ⟫ = 0`.
* `accumulation_sq_of_martingale` — **`√K` accumulation under a genuine filtration**:
  adapted error, martingale-difference increments, bounded conditional second moments.
-/

namespace ShiOptRates.Stochastic

open MeasureTheory Filter
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The real inner product as a continuous bilinear map `E →L[ℝ] E →L[ℝ] ℝ`.

`innerSL` has the conjugate-linear type `E →L⋆[ℝ] E →L[ℝ] ℝ`, which does not unify with
what `condExp_bilin_of_aestronglyMeasurable_left` expects; over `ℝ` the two agree, and this
is that repackaging. -/
noncomputable def innerBilin : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (innerₗ (F := E)) 1 fun x y => by
    simpa using norm_inner_le_norm (𝕜 := ℝ) x y

omit [CompleteSpace E] in
@[simp] theorem innerBilin_apply (x y : E) : innerBilin x y = ⟪x, y⟫_ℝ := rfl

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

end ShiOptRates.Stochastic


