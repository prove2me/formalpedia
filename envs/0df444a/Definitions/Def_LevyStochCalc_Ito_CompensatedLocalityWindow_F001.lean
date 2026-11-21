-- Prove2me | Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F001
-- name    : LevyStochCalc_Ito_CompensatedLocalityWindow_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:52:28.164538+00:00
-- url     : https://prove2.me/theorems/53a16438-6d97-4c13-be92-24ef79632142
-- title:
--   Source declarations: LevyStochCalc.Ito.CompensatedLocalityWindow
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.CompensatedLocalityWindow. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityCutoff_F001

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
/-- The compensated integral depends only on the integrand. -/
theorem stochasticIntegral_congr_fun {ψ : Ω → ℝ → E → ℝ} (h : φ = ψ)
    (hmψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hpψ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hqψ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) (t : ℝ) :
    stochasticIntegral N ℱ hℱ φ hm hp hq t
      = stochasticIntegral N ℱ hℱ ψ hmψ hpψ hqψ t := by
  subst h
  rfl
include hℱ in
/-- **Integrands agreeing at the positive times of a window have the same integral at its
end.** -/
theorem stochasticIntegral_congr_of_eqOn_Ioc {ψ : Ω → ℝ → E → ℝ}
    (hmψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hpψ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hqψ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hagree : ∀ (ω : Ω) (s : ℝ), s ∈ Set.Ioc 0 t → ∀ e, φ ω s e = ψ ω s e) :
    stochasticIntegral N ℱ hℱ φ hm hp hq t
      =ᵐ[P] stochasticIntegral N ℱ hℱ ψ hmψ hpψ hqψ t := by
  refine _root_.Prove2MeSourceProof.h_ba87322c9970bc59472f4ba2 N hℱ φ ψ hm hmψ hp hpψ hq hqψ ht
    (LevyStochCalc.Ito.markedEnergyMeasure_ae_eq_of_ae_ae hm hmψ t ?_)
  refine Eventually.of_forall fun ω => ?_
  have hnull : (volume.restrict (Set.Icc (0 : ℝ) t)) {(0 : ℝ)} = 0 := by simp
  filter_upwards [compl_mem_ae_iff.mpr hnull, ae_restrict_mem measurableSet_Icc] with s hs0 hs
  exact hagree ω s ⟨lt_of_le_of_ne hs.1 (Ne.symm (by simpa using hs0)), hs.2⟩
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
include hm in
/-- Restricting a marked integrand to a time window preserves joint measurability. -/
theorem measurable_indIoc_mul (c t : ℝ) :
    Measurable fun p : Ω × ℝ × E => indIoc Ω c t p.1 p.2.1 * φ p.1 p.2.1 p.2.2 :=
  ((measurable_uncurry_indIoc (Ω := Ω) c t).comp (measurable_fst.prodMk measurable_snd.fst)).mul
    hm
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
include hp in
/-- Restricting a marked integrand to a time window preserves progressive measurability. -/
theorem markedProgressivelyMeasurable_indIoc_mul (c t : ℝ) :
    LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => indIoc Ω c t ω s * φ ω s e := by
  have hfun : (fun ω s e => indIoc Ω c t ω s * φ ω s e)
      = fun ω s e => (Set.Ioc c t).indicator (fun _ => φ ω s e) s := by
    funext ω s e
    by_cases hs : s ∈ Set.Ioc c t <;> simp [indIoc, hs]
  rw [hfun]
  exact hp.indicator_time measurableSet_Ioc
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
include hq in
/-- Restricting a marked integrand to a time window preserves finite energy. -/
theorem sq_int_global_indIoc_mul (c t : ℝ) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖indIoc Ω c t ω s * φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  sq_int_global_of_abs_le (fun ω s e => by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (indIoc_le_one c t ω s)) hq
include hℱ in
/-- The compensated integral at `t` of the integrand restricted to `(0, t]` is the integral at
`t`. -/
theorem stochasticIntegral_indIoc_zero {t : ℝ} (ht : 0 < t) :
    stochasticIntegral N ℱ hℱ (fun ω s e => indIoc Ω 0 t ω s * φ ω s e)
        (measurable_indIoc_mul hm 0 t) (markedProgressivelyMeasurable_indIoc_mul hp 0 t)
        (sq_int_global_indIoc_mul hq 0 t) t
      =ᵐ[P] stochasticIntegral N ℱ hℱ φ hm hp hq t :=
  stochasticIntegral_congr_of_eqOn_Ioc N hℱ (measurable_indIoc_mul hm 0 t)
    (markedProgressivelyMeasurable_indIoc_mul hp 0 t) (sq_int_global_indIoc_mul hq 0 t) hm hp hq
    ht (fun ω s hs e => by simp [indIoc, hs])
include hℱ in
/-- The compensated integral at a nonpositive time vanishes. -/
theorem stochasticIntegral_ae_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    stochasticIntegral N ℱ hℱ φ hm hp hq t =ᵐ[P] 0 :=
  (stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq t).trans
    (_root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N ℱ hℱ φ hm hp hq ht)
end Window

section Linear

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Linear

end LevyStochCalc.Poisson.Compensated


