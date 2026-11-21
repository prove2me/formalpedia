-- Prove2me | Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F000
-- name    : LevyStochCalc_Ito_CompensatedLocalityStopping_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:56:53.261553+00:00
-- url     : https://prove2.me/theorems/727fd11e-0105-4a3f-ac8e-e70283823604
-- title:
--   Source declarations: LevyStochCalc.Ito.CompensatedLocalityStopping
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.CompensatedLocalityStopping. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F001
import Definitions.Def_SourceProof_c420c5d06462fb990bdab16f

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

/-- The piece of a marked integrand on `(c, t]` that the cut at `τ = c` removes. -/
noncomputable def markedCutTerm (c t : ℝ) : Ω → ℝ → E → ℝ :=
  fun ω s e => hitInd τ c ω * (indIoc Ω c t ω s * φ ω s e)
omit [MeasurableSpace E] in
theorem abs_markedCutTerm_le (c t : ℝ) (ω : Ω) (s : ℝ) (e : E) :
    |markedCutTerm τ φ c t ω s e| ≤ |φ ω s e| := by
  have h1 : |hitInd τ c ω| ≤ 1 := abs_hitInd_le_one τ c ω
  have h2 : |indIoc Ω c t ω s| ≤ 1 := indIoc_le_one c t ω s
  calc |markedCutTerm τ φ c t ω s e|
      = |hitInd τ c ω| * (|indIoc Ω c t ω s| * |φ ω s e|) := by
        rw [markedCutTerm, abs_mul, abs_mul]
    _ ≤ 1 * (1 * |φ ω s e|) := by gcongr
    _ = |φ ω s e| := by ring
variable {τ φ}

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


