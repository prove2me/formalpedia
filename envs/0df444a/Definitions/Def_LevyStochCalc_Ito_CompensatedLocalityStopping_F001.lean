-- Prove2me | Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F001
-- name    : LevyStochCalc_Ito_CompensatedLocalityStopping_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:59:34.978916+00:00
-- url     : https://prove2.me/theorems/6e4ea70f-eb4f-44de-822d-9a610fce3ab1
-- title:
--   Source declarations: LevyStochCalc.Ito.CompensatedLocalityStopping
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.CompensatedLocalityStopping. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Optional stopping and locality of the compensated integral

On the window `(0, t]` the integrand cut off at a stopping time of finite range is the integrand
minus, for each value the stopping time takes before `t`, the piece it carries after that value,
so its integral is the integral minus the corresponding increments; a general stopping time is
the decreasing limit of its grid approximations, whose cut-off integrands converge in energy, and
the difference isometry squeezes the integrals, so two marked integrands agreeing up to — or
strictly before — a stopping time have the same compensated integral at every time the stopping
time has not reached.

## Main definitions

* `markedCutTerm τ φ c t` — the piece of `φ` on `(c, t]` that the cut at `τ = c` removes.

## Main statements

* `stochasticIntegral_markedStopped_finiteRange` — optional stopping at a stopping time of
  finite range.
* `stochasticIntegral_markedStopped_eq_of_le` — at a time the stopping time has not reached,
  cutting the integrand off at it changes nothing.
* `stochasticIntegral_congr_of_le`, `stochasticIntegral_congr_of_lt` — integrands agreeing up
  to (respectively, strictly before) a stopping time have the same integral at every time the
  stopping time has not reached.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito (indIoc indIoc_le_one hitInd abs_hitInd_le_one measurable_hitInd
  stronglyMeasurable_hitInd gridStop gridPt isStoppingTime_gridStop le_gridStop gridPt_nonneg
  gridPt_lt_of_lt gridStop_finiteRange sq_nnnorm_sub_le_two_mul)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section FiniteRange

variable (τ : Ω → WithTop ℝ) (φ : Ω → ℝ → E → ℝ)

variable {τ φ}

/-- The removed piece is jointly measurable. -/
theorem measurable_markedCutTerm (hτ : IsStoppingTime ℱ τ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (c t : ℝ) :
    Measurable fun p : Ω × ℝ × E => markedCutTerm τ φ c t p.1 p.2.1 p.2.2 :=
  ((measurable_hitInd τ hτ c).comp measurable_fst).mul (measurable_indIoc_mul hm c t)
/-- The removed piece is progressively measurable. -/
theorem markedProgressivelyMeasurable_markedCutTerm (hτ : IsStoppingTime ℱ τ)
    (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ) (c t : ℝ) :
    LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ (markedCutTerm τ φ c t) :=
  _root_.Prove2MeSourceProof.h_ec4d5d34845b027c60491406
    (markedProgressivelyMeasurable_indIoc_mul hp c t)
    (fun ω s e hs => by
      have : s ∉ Set.Ioc c t := fun h => absurd h.1 (not_lt.mpr hs)
      simp [indIoc, this])
    (stronglyMeasurable_hitInd τ hτ c)
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The removed piece has finite energy. -/
theorem sq_int_global_markedCutTerm
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) (c t : ℝ) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖markedCutTerm τ φ c t ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  sq_int_global_of_abs_le (fun ω s e => abs_markedCutTerm_le τ φ c t ω s e) hq
variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end FiniteRange

section Local

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  {τ : Ω → WithTop ℝ}
  {φ : Ω → ℝ → E → ℝ} (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Local

end LevyStochCalc.Poisson.Compensated


