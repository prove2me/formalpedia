-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimpleProfile_F001
-- name    : LevyStochCalc_Poisson_SimpleProfile_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:31:38.654239+00:00
-- url     : https://prove2.me/theorems/0ce881a5-e559-4b22-955e-63d6ad5eeb92
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimpleProfile
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimpleProfile. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleProfile_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple mark profiles and their compensated step integrals

A *simple mark profile* for an intensity `ν` on the mark space is a finite family of pairwise
disjoint mark sets of finite intensity carrying constant coefficients, `∑ₖ cₖ 𝟙_{Bₖ}`. Every
square-integrable mark profile is the `L²(ν)` limit of simple profiles, obtained from the nonzero
level sets of square-integrable simple functions approximating it in `L²(ν)`; a bounded one is
the limit of simple profiles obeying the same bound, obtained from the simple functions
approximating it inside the interval the bound cuts out.

The compensated integral of a simple profile over the step `(a, b]` is
`∑ₖ cₖ Ñ((a, b] × Bₖ)`. The `L²(P)` pairing of two such integrals over a common step is
`(b − a) ∫ f g dν`, so profiles converging in `L²(ν)` have compensated integrals converging in
`L²(P)`.

## Main definitions

* `LevyStochCalc.Poisson.SimpleProfile` — a simple mark profile.
* `LevyStochCalc.Poisson.SimpleProfile.toFun` — the function it carries.
* `LevyStochCalc.Poisson.SimpleProfile.stepIntegral` — its compensated integral over a step.

## Main statements

* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2_of_memLp` — approximation of a
  square-integrable mark profile by simple profiles.
* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2` — approximation of a bounded
  square-integrable mark profile by simple profiles obeying the same bound.
* `LevyStochCalc.Poisson.SimpleProfile.integral_stepIntegral_mul` — the `L²(P)` pairing of two
  compensated step integrals.
* `LevyStochCalc.Poisson.SimpleProfile.eLpNorm_stepIntegral_sub` — the isometry
  `‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}`.
* `LevyStochCalc.Poisson.exists_memLp_tendsto_stepIntegral` — convergence of the compensated
  integrals in `L²(P)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

namespace SimpleProfile

/-! ### The compensated integral of a simple profile over a step -/

/-- The compensated integral of a simple mark profile over the step `(a, b]`. -/
noncomputable def stepIntegral (G : SimpleProfile E ν) (N : PoissonRandomMeasure P ν)
    (a b : ℝ) (ω : Ω) : ℝ :=
  ∑ k, G.c k * N.compensated (Set.Ioc a b ×ˢ G.B k) ω
variable (N : PoissonRandomMeasure P ν)

/-- The compensated measure of a step times a mark set of a simple profile is square
integrable. -/
theorem memLp_compensated_step (G : SimpleProfile E ν) {a : ℝ} (ha : 0 ≤ a) (b : ℝ)
    (k : Fin G.K) :
    MemLp (fun ω => N.compensated (Set.Ioc a b ×ˢ G.B k) ω) 2 P :=
  Compensated.compensated_memLp N (measurableSet_Ioc.prod (G.B_measurable k))
    (by rw [referenceIntensity_Ioc_prod' _ ha]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (G.B_finite k))
/-- The compensated step integral of a simple mark profile is square integrable. -/
theorem memLp_stepIntegral (G : SimpleProfile E ν) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    MemLp (G.stepIntegral N a b) 2 P :=
  memLp_finsetSum _ fun k _ => (G.memLp_compensated_step N ha b k).const_mul _
/-! ### Simple profiles from simple functions -/

end SimpleProfile

/-! ### Approximation of a square-integrable mark profile -/

/-! ### Convergence of the compensated step integrals -/

end LevyStochCalc.Poisson


