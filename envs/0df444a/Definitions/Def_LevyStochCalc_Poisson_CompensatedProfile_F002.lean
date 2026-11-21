-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProfile_F002
-- name    : LevyStochCalc_Poisson_CompensatedProfile_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:34:10.181062+00:00
-- url     : https://prove2.me/theorems/a516040d-a86d-4eeb-9bd7-494a5285e6a8
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProfile
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProfile. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfile_F001
import Definitions.Def_SourceProof_722eb9b2cd962b654329cb6c

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral of a deterministic mark profile over a step

The compensated step integrals of simple mark profiles obey the isometry
`‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}`, so an `L²(P)` limit of the compensated step
integrals of simple profiles converging in `L²(ν)` is determined, up to a null set, by the limit
profile alone. That limit is the compensated integral over the step `(a, b]` of a
square-integrable deterministic mark profile `f : E → ℝ` against a Poisson random measure with
intensity `ν`. It agrees with the compensated step integral at a simple profile and carries the
Lévy character

  `E[exp (i u J(f))] = exp ((b − a) ∫ (exp (i u f) − 1 − i u f) dν)`.

## Main definitions

* `LevyStochCalc.Poisson.IsCompensatedProfile` — being a strongly measurable `L²(P)` limit at a
  step of the compensated step integrals of every sequence of simple mark profiles converging to
  a mark profile in `L²(ν)`.
* `LevyStochCalc.Poisson.compensatedProfile` — the compensated integral of a square-integrable
  deterministic mark profile over a step.

## Main statements

* `LevyStochCalc.Poisson.ae_eq_of_tendsto_stepIntegral` — an `L²(P)` limit of the compensated
  step integrals of simple profiles converging in `L²(ν)` depends only on the limit profile.
* `LevyStochCalc.Poisson.stronglyMeasurable_compensatedProfile`,
  `LevyStochCalc.Poisson.memLp_compensatedProfile` — measurability and square integrability.
* `LevyStochCalc.Poisson.tendsto_stepIntegral_compensatedProfile` — the compensated step
  integrals of simple profiles converging to a profile in `L²(ν)` converge to its compensated
  integral in `L²(P)`.
* `LevyStochCalc.Poisson.compensatedProfile_toFun` — agreement with the compensated step
  integral at a simple mark profile.
* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile` — the Lévy character of the
  compensated integral of a mark profile over a step.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Independence of the approximating sequence -/

/-! ### The compensated integral of a mark profile over a step -/

/-! ### Agreement at a simple mark profile -/

/-! ### The character -/

/-- **The character of the compensated integral of a mark profile over a step.** -/
theorem integral_exp_I_mul_compensatedProfile (N : PoissonRandomMeasure P ν) {f : E → ℝ}
    (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (G : ℕ → SimpleProfile E ν)
    (hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (nhds 0))
    (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N f a b ω : ℝ) : ℂ)) ∂P
      = Complex.exp (((b - a : ℝ) : ℂ) * ∫ e, levyCharIntegrand u (f e) ∂ν) :=
  _root_.Prove2MeSourceProof.h_722eb9b2cd962b654329cb6c N G hf ha hab
    (memLp_compensatedProfile N f a b) hG
    (tendsto_stepIntegral_compensatedProfile N hf ha hab G hG) u
/-- The character of the compensated integral of a square-integrable mark profile over a
step. -/
theorem integral_exp_I_mul_compensatedProfile_of_memLp (N : PoissonRandomMeasure P ν)
    {f : E → ℝ} (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N f a b ω : ℝ) : ℂ)) ∂P
      = Complex.exp (((b - a : ℝ) : ℂ) * ∫ e, levyCharIntegrand u (f e) ∂ν) := by
  obtain ⟨G, hG⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hf
  exact integral_exp_I_mul_compensatedProfile N hf ha hab G hG u
end LevyStochCalc.Poisson


