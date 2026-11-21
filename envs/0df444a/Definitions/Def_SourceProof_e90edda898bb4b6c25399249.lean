-- Prove2me | Definitions.Def_SourceProof_e90edda898bb4b6c25399249
-- name    : SourceProof_e90edda898bb4b6c25399249
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:56:43.297965+00:00
-- url     : https://prove2.me/theorems/1f64723f-289b-4d78-85d4-880e53457f91
-- title:
--   LevyStochCalc source module: SourceProof_e90edda898bb4b6c25399249
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stochasticIntegral_indicator_Ioc` comes from the `LevyStochCalc.Ito.CompensatedLocalityWindow` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F001
import Definitions.Def_SourceProof_5a9b6e7ab698681a1e363ba1

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral over a time window

Restricting a marked integrand to a window `(c, t]` preserves admissibility and yields the
increment of the compensated integral across that window; an integrand vanishing after a
positive time `c` has an integral that no longer moves after `c`, the hit indicator of a
stopping time at `c` factors out of the integral over `(c, t]`, and the integral is additive in
the integrand, over differences and over finite sums.

## Main statements

* `stochasticIntegral_ae_eq_of_vanishing_gt` — the integral of an integrand vanishing after a
  time `c` does not move after `c`.
* `stochasticIntegral_indicator_Ioc` — restricting the integrand to `(c, t]` gives the increment
  of the integral over `(c, t]`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito (indIoc indIoc_le_one measurable_uncurry_indIoc hitInd
  abs_hitInd_le_one stronglyMeasurable_hitInd sq_nnnorm_add_le_two_mul)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Window

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  {φ : Ω → ℝ → E → ℝ}
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_e90edda898bb4b6c25399249 {c t : ℝ} (hc : 0 ≤ c) (hct : c < t) :
    stochasticIntegral N ℱ hℱ (fun ω s e => indIoc Ω c t ω s * φ ω s e)
        (measurable_indIoc_mul hm c t) (markedProgressivelyMeasurable_indIoc_mul hp c t)
        (sq_int_global_indIoc_mul hq c t) t
      =ᵐ[P] fun ω => stochasticIntegral N ℱ hℱ φ hm hp hq t ω
        - stochasticIntegral N ℱ hℱ φ hm hp hq c ω := by
  have ht : 0 < t := hc.trans_lt hct
  -- the window `(0, t]` splits at `c`
  have hsplit : (fun ω s e => LevyStochCalc.Brownian.Ito.indIoc Ω 0 t ω s * φ ω s e)
      = fun ω s e => LevyStochCalc.Brownian.Ito.indIoc Ω 0 c ω s * φ ω s e + LevyStochCalc.Brownian.Ito.indIoc Ω c t ω s * φ ω s e := by
    funext ω s e
    simp only [LevyStochCalc.Brownian.Ito.indIoc]
    by_cases h1 : s ∈ Set.Ioc (0 : ℝ) c
    · have h2 : s ∈ Set.Ioc (0 : ℝ) t := ⟨h1.1, h1.2.trans hct.le⟩
      have h3 : s ∉ Set.Ioc c t := fun h => absurd h.1 (not_lt.mpr h1.2)
      simp [h1, h2, h3]
    · by_cases h3 : s ∈ Set.Ioc c t
      · have h2 : s ∈ Set.Ioc (0 : ℝ) t := ⟨hc.trans_lt h3.1, h3.2⟩
        simp [h1, h2, h3]
      · have h2 : s ∉ Set.Ioc (0 : ℝ) t := fun h => by
          rcases le_or_gt s c with hsc | hsc
          · exact h1 ⟨h.1, hsc⟩
          · exact h3 ⟨hsc, h.2⟩
        simp [h1, h2, h3]
  have hm0 := LevyStochCalc.Poisson.Compensated.measurable_indIoc_mul hm 0 c
  have hp0 := LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_indIoc_mul hp 0 c
  have hq0 := LevyStochCalc.Poisson.Compensated.sq_int_global_indIoc_mul hq 0 c
  have hma := LevyStochCalc.Poisson.Compensated.measurable_uncurry_congr hsplit (LevyStochCalc.Poisson.Compensated.measurable_indIoc_mul hm 0 t)
  have hpa := LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_congr hsplit
    (LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_indIoc_mul hp 0 t)
  have hqa := LevyStochCalc.Poisson.Compensated.sq_int_global_congr hsplit (LevyStochCalc.Poisson.Compensated.sq_int_global_indIoc_mul hq 0 t)
  have hadd := _root_.Prove2MeSourceProof.h_79a6cde54e31b0f9d920e0b6 N ℱ hℱ hm0 (LevyStochCalc.Poisson.Compensated.measurable_indIoc_mul hm c t) hp0
    (LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_indIoc_mul hp c t) hq0 (LevyStochCalc.Poisson.Compensated.sq_int_global_indIoc_mul hq c t)
    hma hpa hqa ht
  have hzero := LevyStochCalc.Poisson.Compensated.stochasticIntegral_indIoc_zero N hℱ hm hp hq ht
  rw [LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_fun N hℱ (LevyStochCalc.Poisson.Compensated.measurable_indIoc_mul hm 0 t)
    (LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_indIoc_mul hp 0 t) (LevyStochCalc.Poisson.Compensated.sq_int_global_indIoc_mul hq 0 t) hsplit
    hma hpa hqa t] at hzero
  -- the first piece is the integral at `c`
  have hfirst : LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (fun ω s e => LevyStochCalc.Brownian.Ito.indIoc Ω 0 c ω s * φ ω s e)
        hm0 hp0 hq0 t
      =ᵐ[P] LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq c := by
    rcases hc.lt_or_eq with hc' | hc'
    · have h1 := _root_.Prove2MeSourceProof.h_5a9b6e7ab698681a1e363ba1 N hℱ hm0 hp0 hq0 hc' hct.le
        (fun ω s e hs => by
          have : s ∉ Set.Ioc (0 : ℝ) c := fun h => absurd h.2 (not_le.mpr hs)
          simp [LevyStochCalc.Brownian.Ito.indIoc, this])
      exact h1.trans (LevyStochCalc.Poisson.Compensated.stochasticIntegral_indIoc_zero N hℱ hm hp hq hc')
    · subst hc'
      have h1 : LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (fun ω s e => LevyStochCalc.Brownian.Ito.indIoc Ω 0 0 ω s * φ ω s e)
            hm0 hp0 hq0 t
          =ᵐ[P] 0 :=
        _root_.Prove2MeSourceProof.h_1da9cef3cd7392595155fa63 N hℱ _ hm0 hp0 hq0 ht.le
          (fun ω s e _ => by simp [LevyStochCalc.Brownian.Ito.indIoc])
      exact h1.trans (LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ hm hp hq le_rfl).symm
  filter_upwards [hadd, hzero, hfirst] with ω h1 h2 h3
  rw [← h2, h1, h3]
  ring
end Window

section Linear

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Linear

end LevyStochCalc.Poisson.Compensated


