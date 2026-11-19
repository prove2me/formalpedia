-- Prove2me | Definitions.Def_LevyStochCalc_Probability_Quasimartingale_F000
-- name    : LevyStochCalc_Probability_Quasimartingale_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:43:21.995459+00:00
-- url     : https://prove2.me/theorems/865f8dc4-dc8b-404d-a30c-88ce9d387cfe
-- title:
--   Source declarations: LevyStochCalc.Probability.Quasimartingale
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.Quasimartingale. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_Basic_F000
import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Martingales are real quasimartingales

The elementary stochastic integral of the indicator of an elementary predictable set against a
process `X` is a finite sum of terms `1_{B}·(X_{b ⊓ t} − X_{a ⊓ t})` with `B ∈ ℱ_a`. For a
martingale each such term has mean zero, so the variation of `X` in the sense of
`ProbabilityTheory.IsRealQuasimartingale` is bounded by `0`.

## Main statements

* `integral_indicator_martingale_eq_zero` — the elementary integral has mean zero.
* `isRealQuasimartingale_of_martingale` — a martingale is a real quasimartingale.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory.SimpleProcess

namespace LevyStochCalc.Probability

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω}
  {𝓕 : Filtration ι mΩ} {μ : Measure Ω} {X : ι → Ω → ℝ}

/-- Stopping a process at a constant time evaluates it at the minimum of the two times. -/
theorem stoppedProcess_const (X : ι → Ω → ℝ) (t i : ι) (ω : Ω) :
    stoppedProcess X (fun _ => (t : WithTop ι)) i ω = X (min i t) ω := by
  rw [MeasureTheory.stoppedProcess, ← WithTop.coe_inf]
  rfl
/-- **The elementary integral of a martingale against an elementary predictable indicator has
mean zero.** -/
theorem integral_indicator_martingale_eq_zero [IsFiniteMeasure μ] (hX : Martingale X 𝓕 μ)
    (S : ElementaryPredictableSet 𝓕) (t : ι) :
    μ[(S.indicator (1 : ℝ) ● X) t] = 0 := by
  have hint : ∀ s, Integrable (X s) μ := hX.integrable
  have hmeas : ∀ p ∈ S.I, MeasurableSet (S.set p) :=
    fun p hp => 𝓕.le p.1 _ (S.measurableSet_set p hp)
  have hpt : ∀ ω, (S.indicator (1 : ℝ) ● X) t ω
      = ∑ p ∈ S.I, (S.set p).indicator (fun ω => X (min p.2 t) ω - X (min p.1 t) ω) ω := by
    intro ω
    rw [ElementaryPredictableSet.integral_indicator_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [stoppedProcess_const]
  simp_rw [hpt]
  rw [integral_finsetSum (f := fun p : ι × ι => (S.set p).indicator
      (fun ω => X (min p.2 t) ω - X (min p.1 t) ω)) _
    fun p hp => ((hint _).sub (hint _)).indicator (hmeas p hp)]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hB : MeasurableSet[𝓕 p.1] (S.set p) := S.measurableSet_set p hp
  rw [integral_indicator (hmeas p hp),
    integral_sub ((hint _).integrableOn) ((hint _).integrableOn)]
  rcases le_or_gt t p.1 with h | h
  · rw [min_eq_right h, min_eq_right (h.trans (S.le_of_mem_I p hp))]
    ring
  · rw [min_eq_left h.le, ← hX.setIntegral_eq (le_min (S.le_of_mem_I p hp) h.le) hB]
    ring
/-- **A martingale is a real quasimartingale**, with variation bound `0`. -/
theorem isRealQuasimartingale_of_martingale [IsFiniteMeasure μ] (hX : Martingale X 𝓕 μ) :
    IsRealQuasimartingale 𝓕 X μ :=
  ⟨hX.stronglyAdapted.adapted, hX.integrable,
    fun t => ⟨0, fun S => (integral_indicator_martingale_eq_zero hX S t).le⟩⟩
end LevyStochCalc.Probability


