-- Prove2me | Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F002
-- name    : LevyStochCalc_Ito_CompensatedLocalityStopping_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:14:49.320322+00:00
-- url     : https://prove2.me/theorems/6f7fd77b-d825-470d-906c-9db16923fd9a
-- title:
--   LevyStochCalc source module: LevyStochCalc.Ito.CompensatedLocalityStopping
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Ito.CompensatedLocalityStopping in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F001
import Definitions.Def_SourceProof_68dd6350f3aeefa2416beba6
import Definitions.Def_SourceProof_a108b20c3c7f7ed49b14b48f
import Definitions.Def_SourceProof_c420c5d06462fb990bdab16f
import Definitions.Def_SourceProof_d125007308283836842bb087

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

include hℱ in
/-- **Two marked integrands agreeing up to a stopping time have the same compensated integral
at a time that stopping time has not reached.** -/
theorem stochasticIntegral_congr_of_le (hτ : IsStoppingTime ℱ τ) {ψ : Ω → ℝ → E → ℝ}
    (hmψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hpψ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hqψ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ τ ω →
      ∀ e, φ ω s e = ψ ω s e)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegral N ℱ hℱ φ hm hp hq t ω
        = stochasticIntegral N ℱ hℱ ψ hmψ hpψ hqψ t ω := by
  have e1 := _root_.Prove2MeSourceProof.h_d125007308283836842bb087 N hℱ hm hp hq hτ ht
  have e2 := _root_.Prove2MeSourceProof.h_d125007308283836842bb087 N hℱ (φ := ψ) hmψ hpψ hqψ hτ ht
  have hstop : ∀ (ω : Ω) (s : ℝ), 0 < s → ∀ e,
      markedStopped τ φ ω s e = markedStopped τ ψ ω s e := by
    intro ω s hs e
    unfold markedStopped
    by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
    · rw [if_pos hle, if_pos hle, hagree ω s hs hle e]
    · rw [if_neg hle, if_neg hle]
  have e3 := stochasticIntegral_congr_of_pos N hℱ (_root_.Prove2MeSourceProof.h_68dd6350f3aeefa2416beba6 hτ hm)
    (_root_.Prove2MeSourceProof.h_a108b20c3c7f7ed49b14b48f hτ hp) (sq_int_global_markedStopped hq)
    (_root_.Prove2MeSourceProof.h_68dd6350f3aeefa2416beba6 hτ hmψ) (_root_.Prove2MeSourceProof.h_a108b20c3c7f7ed49b14b48f hτ hpψ)
    (sq_int_global_markedStopped hqψ) hstop ht
  filter_upwards [e1, e2, e3] with ω h1 h2 h3 hle
  rw [← h1 hle, ← h2 hle, h3]
include hℱ in
/-- **Two marked integrands agreeing strictly before a stopping time have the same compensated
integral at a time that stopping time has not reached.** -/
theorem stochasticIntegral_congr_of_lt (hτ : IsStoppingTime ℱ τ) {ψ : Ω → ℝ → E → ℝ}
    (hmψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hpψ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hqψ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) < τ ω →
      ∀ e, φ ω s e = ψ ω s e)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegral N ℱ hℱ φ hm hp hq t ω
        = stochasticIntegral N ℱ hℱ ψ hmψ hpψ hqψ t ω := by
  have e1 := _root_.Prove2MeSourceProof.h_d125007308283836842bb087 N hℱ hm hp hq hτ ht
  have e2 := _root_.Prove2MeSourceProof.h_d125007308283836842bb087 N hℱ (φ := ψ) hmψ hpψ hqψ hτ ht
  -- the cut integrands agree off the time `0` and the value of the stopping time
  have hstop : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), ∀ e,
      markedStopped τ φ ω s e = markedStopped τ ψ ω s e := by
    refine Eventually.of_forall fun ω => ?_
    have hnull : (volume.restrict (Set.Icc (0 : ℝ) t))
        ({(0 : ℝ)} ∪ {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ ω}) = 0 := by
      refine measure_union_null (by simp) ?_
      rcases eq_or_ne (τ ω) ⊤ with hτω | hτω
      · have hempty : {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ ω} = ∅ := by
          ext s
          simp [hτω]
        rw [hempty]
        exact measure_empty
      · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hτω
        have hsing : {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ ω} = {r} := by
          ext s
          rw [Set.mem_setOf_eq, Set.mem_singleton_iff, ← hr]
          exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
        rw [hsing]
        simp
    filter_upwards [compl_mem_ae_iff.mpr hnull, ae_restrict_mem measurableSet_Icc]
      with s hs0 hs e
    have hsn : ¬ s = 0 ∧ ¬ ((s : ℝ) : WithTop ℝ) = τ ω := by
      simpa [not_or] using hs0
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsn.1)
    unfold markedStopped
    by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
    · rw [if_pos hle, if_pos hle, hagree ω s hspos (lt_of_le_of_ne hle hsn.2) e]
    · rw [if_neg hle, if_neg hle]
  have e3 := _root_.Prove2MeSourceProof.h_ba87322c9970bc59472f4ba2 N hℱ (markedStopped τ φ) (markedStopped τ ψ)
    (_root_.Prove2MeSourceProof.h_68dd6350f3aeefa2416beba6 hτ hm) (_root_.Prove2MeSourceProof.h_68dd6350f3aeefa2416beba6 hτ hmψ)
    (_root_.Prove2MeSourceProof.h_a108b20c3c7f7ed49b14b48f hτ hp)
    (_root_.Prove2MeSourceProof.h_a108b20c3c7f7ed49b14b48f hτ hpψ)
    (sq_int_global_markedStopped hq) (sq_int_global_markedStopped hqψ) ht
    (LevyStochCalc.Ito.markedEnergyMeasure_ae_eq_of_ae_ae (_root_.Prove2MeSourceProof.h_68dd6350f3aeefa2416beba6 hτ hm)
      (_root_.Prove2MeSourceProof.h_68dd6350f3aeefa2416beba6 hτ hmψ) t hstop)
  filter_upwards [e1, e2, e3] with ω h1 h2 h3 hle
  rw [← h1 hle, ← h2 hle, h3]
end Local

end LevyStochCalc.Poisson.Compensated


