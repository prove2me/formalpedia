-- Prove2me | Definitions.Def_SourceProof_df70248aed5926ac78d4f250
-- name    : SourceProof_df70248aed5926ac78d4f250
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:03:43.312941+00:00
-- url     : https://prove2.me/theorems/22e8fb0e-dc04-46ac-b161-87352c370f65
-- title:
--   LevyStochCalc source module: SourceProof_df70248aed5926ac78d4f250
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stochasticIntegral_markedStopped_finiteRange` comes from the `LevyStochCalc.Ito.CompensatedLocalityStopping` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F001
import Definitions.Def_SourceProof_68dd6350f3aeefa2416beba6
import Definitions.Def_SourceProof_6cdc47526d2ae213604fd2f4
import Definitions.Def_SourceProof_78ebf7438df184d60f260ac5
import Definitions.Def_SourceProof_a108b20c3c7f7ed49b14b48f
import Definitions.Def_SourceProof_e083995b3996f253464d63f5
import Definitions.Def_SourceProof_e90edda898bb4b6c25399249
import Definitions.Def_SourceProof_f083182fb41b088ede72a109

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

include hℱ in

theorem _root_.Prove2MeSourceProof.h_df70248aed5926ac78d4f250 (hτ : IsStoppingTime ℱ τ)
    {t : ℝ} (ht : 0 < t) (J : Finset ℝ) (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ))
      ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    stochasticIntegral N ℱ hℱ (markedStopped τ φ) (_root_.Prove2MeSourceProof.h_68dd6350f3aeefa2416beba6 hτ hm)
        (_root_.Prove2MeSourceProof.h_a108b20c3c7f7ed49b14b48f hτ hp) (sq_int_global_markedStopped hq) t
      =ᵐ[P] fun ω => stochasticIntegral N ℱ hℱ φ hm hp hq t ω
        - ∑ c ∈ J, hitInd τ c ω * (stochasticIntegral N ℱ hℱ φ hm hp hq t ω
            - stochasticIntegral N ℱ hℱ φ hm hp hq c ω) := by
  classical
  have hmS := _root_.Prove2MeSourceProof.h_68dd6350f3aeefa2416beba6 hτ hm
  have hpS := _root_.Prove2MeSourceProof.h_a108b20c3c7f7ed49b14b48f hτ hp
  have hqS := LevyStochCalc.Poisson.Compensated.sq_int_global_markedStopped (τ := τ) hq
  have hmI0 := LevyStochCalc.Poisson.Compensated.measurable_indIoc_mul hm 0 t
  have hpI0 := LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_indIoc_mul hp 0 t
  have hqI0 := LevyStochCalc.Poisson.Compensated.sq_int_global_indIoc_mul hq 0 t
  have hmW := LevyStochCalc.Poisson.Compensated.measurable_indIoc_mul hmS 0 t
  have hpW := LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_indIoc_mul hpS 0 t
  have hqW := LevyStochCalc.Poisson.Compensated.sq_int_global_indIoc_mul hqS 0 t
  have hmF : ∀ c : ℝ,
      Measurable fun p : Ω × ℝ × E => LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t p.1 p.2.1 p.2.2 :=
    fun c => LevyStochCalc.Poisson.Compensated.measurable_markedCutTerm hτ hm c t
  have hpF : ∀ c : ℝ, LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      (LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t) :=
    fun c => LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_markedCutTerm hτ hp c t
  have hqF : ∀ (c T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun c => LevyStochCalc.Poisson.Compensated.sq_int_global_markedCutTerm hq c t
  obtain ⟨hmSum, hpSum, hqSum, hSum⟩ := _root_.Prove2MeSourceProof.h_f083182fb41b088ede72a109 N hℱ
    (fun c : ℝ => LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t) hmF hpF hqF J ht
  have hmD : Measurable fun p : Ω × ℝ × E => LevyStochCalc.Brownian.Ito.indIoc Ω 0 t p.1 p.2.1 * φ p.1 p.2.1 p.2.2
      - ∑ c ∈ J, LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t p.1 p.2.1 p.2.2 := hmI0.sub hmSum
  have hpD : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => LevyStochCalc.Brownian.Ito.indIoc Ω 0 t ω s * φ ω s e - ∑ c ∈ J, LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t ω s e :=
    LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_sub hpI0 hpSum
  have hqD : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖LevyStochCalc.Brownian.Ito.indIoc Ω 0 t ω s * φ ω s e
        - ∑ c ∈ J, LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t ω s e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P < ⊤ :=
    LevyStochCalc.Poisson.Compensated.markedEnergy_lt_top_of_bound (fun _ _ _ => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hmI0 hmSum hqI0
      hqSum
  have hpath : (fun ω s e => LevyStochCalc.Brownian.Ito.indIoc Ω 0 t ω s * LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e)
      = fun ω s e => LevyStochCalc.Brownian.Ito.indIoc Ω 0 t ω s * φ ω s e
        - ∑ c ∈ J, LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t ω s e :=
    _root_.Prove2MeSourceProof.h_e083995b3996f253464d63f5 τ φ J hJ0 hJt hτJ
  have hterm : ∀ c ∈ J,
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t) (hmF c) (hpF c) (hqF c) t
        =ᵐ[P] fun ω => LevyStochCalc.Brownian.Ito.hitInd τ c ω * (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq c ω) := by
    intro c hc
    have hc0 : 0 ≤ c := hJ0 c hc
    have hct : c < t := hJt c hc
    have hpull := _root_.Prove2MeSourceProof.h_78ebf7438df184d60f260ac5 N hℱ hm hp hq hτ hc0 hct (hmF c) (hpF c)
      (hqF c)
    have hloc := _root_.Prove2MeSourceProof.h_e90edda898bb4b6c25399249 N hℱ hm hp hq hc0 hct
    filter_upwards [hpull, hloc] with ω hpullω hlocω
    have hpull' : LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t) (hmF c) (hpF c) (hqF c)
          t ω
        = LevyStochCalc.Brownian.Ito.hitInd τ c ω * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ
          (fun ω s e => LevyStochCalc.Brownian.Ito.indIoc Ω c t ω s * φ ω s e) (LevyStochCalc.Poisson.Compensated.measurable_indIoc_mul hm c t)
          (LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_indIoc_mul hp c t) (LevyStochCalc.Poisson.Compensated.sq_int_global_indIoc_mul hq c t)
          t ω := hpullω
    rw [hpull', hlocω]
  have hstep := LevyStochCalc.Poisson.Compensated.stochasticIntegral_indIoc_zero N hℱ hmS hpS hqS ht
  have hcongr := LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_fun N hℱ hmW hpW hqW hpath hmD hpD hqD t
  have hsub := _root_.Prove2MeSourceProof.h_6cdc47526d2ae213604fd2f4 N hℱ hmI0 hmSum hpI0 hpSum hqI0 hqSum hmD hpD hqD ht
  have hI0 := LevyStochCalc.Poisson.Compensated.stochasticIntegral_indIoc_zero N hℱ hm hp hq ht
  have hall : ∀ᵐ ω ∂P, ∀ c ∈ (↑J : Set ℝ),
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t) (hmF c) (hpF c) (hqF c) t ω
        = LevyStochCalc.Brownian.Ito.hitInd τ c ω * (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq c ω) :=
    (MeasureTheory.ae_ball_iff J.countable_toSet).mpr fun c hc => hterm c (Finset.mem_coe.mp hc)
  filter_upwards [hstep, hsub, hI0, hSum, hall] with ω h1 h3 h4 h5 h6
  have h2 := congrFun hcongr ω
  rw [← h1, h2, h3, h4, h5, Finset.sum_congr rfl fun c hc => h6 c (Finset.mem_coe.mpr hc)]
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


