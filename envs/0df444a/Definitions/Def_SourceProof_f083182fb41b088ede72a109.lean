-- Prove2me | Definitions.Def_SourceProof_f083182fb41b088ede72a109
-- name    : SourceProof_f083182fb41b088ede72a109
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:56:53.04417+00:00
-- url     : https://prove2.me/theorems/7e07358e-cddf-4eca-a9f9-09c6b55c991a
-- title:
--   LevyStochCalc source module: SourceProof_f083182fb41b088ede72a109
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.exists_stochasticIntegral_finsetSum` comes from the `LevyStochCalc.Ito.CompensatedLocalityWindow` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F001

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

end Window

section Linear

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_f083182fb41b088ede72a109 {ι : Type*}
    (H : ι → Ω → ℝ → E → ℝ)
    (hmH : ∀ i, Measurable fun p : Ω × ℝ × E => H i p.1 p.2.1 p.2.2)
    (hpH : ∀ i, LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ (H i))
    (hqH : ∀ (i : ι) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖H i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (J : Finset ι) {T : ℝ} (hT : 0 < T) :
    ∃ (hms : Measurable fun p : Ω × ℝ × E => ∑ i ∈ J, H i p.1 p.2.1 p.2.2)
      (hps : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
        fun ω s e => ∑ i ∈ J, H i ω s e)
      (hqs : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖∑ i ∈ J, H i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
      stochasticIntegral N ℱ hℱ (fun ω s e => ∑ i ∈ J, H i ω s e) hms hps hqs T
        =ᵐ[P] fun ω => ∑ i ∈ J,
          stochasticIntegral N ℱ hℱ (H i) (hmH i) (hpH i) (hqH i) T ω := by
  classical
  induction J using Finset.induction with
  | empty =>
    have hfun : (fun (ω : Ω) (s : ℝ) (e : E) => ∑ i ∈ (∅ : Finset ι), H i ω s e)
        = fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ) := by
      funext ω s e
      simp
    have hmz : Measurable fun (_ : Ω × ℝ × E) => (0 : ℝ) := measurable_const
    have hpz : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
        fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ) := LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ
    have hqz : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ _s in Set.Icc (0 : ℝ) T', ∫⁻ _e,
        (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
      intro T' _
      simp
    refine ⟨LevyStochCalc.Poisson.Compensated.measurable_uncurry_congr hfun.symm hmz,
      LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_congr hfun.symm hpz, LevyStochCalc.Poisson.Compensated.sq_int_global_congr hfun.symm hqz, ?_⟩
    rw [LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_fun N hℱ
      (φ := fun (ω : Ω) (s : ℝ) (e : E) => ∑ i ∈ (∅ : Finset ι), H i ω s e) _ _ _ hfun
      hmz hpz hqz T]
    filter_upwards [_root_.Prove2MeSourceProof.h_1da9cef3cd7392595155fa63 N hℱ
      (fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ)) hmz hpz hqz hT.le (fun _ _ _ _ => rfl)]
      with ω hω
    simpa using hω
  | insert a J ha ih =>
    obtain ⟨hms, hps, hqs, hae⟩ := ih
    have hfun : (fun (ω : Ω) (s : ℝ) (e : E) => ∑ i ∈ insert a J, H i ω s e)
        = fun ω s e => H a ω s e + ∑ i ∈ J, H i ω s e := by
      funext ω s e
      exact Finset.sum_insert ha
    have hma : Measurable fun p : Ω × ℝ × E =>
        H a p.1 p.2.1 p.2.2 + ∑ i ∈ J, H i p.1 p.2.1 p.2.2 := (hmH a).add hms
    have hpa : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
        fun ω s e => H a ω s e + ∑ i ∈ J, H i ω s e :=
      _root_.Prove2MeSourceProof.h_67a5d0b973066b3e65d99ba2 (hpH a) hps
    have hqa : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖H a ω s e + ∑ i ∈ J, H i ω s e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤ :=
      LevyStochCalc.Poisson.Compensated.markedEnergy_lt_top_of_bound (fun _ _ _ => LevyStochCalc.Poisson.Compensated.sq_nnnorm_add_le_two_mul _ _) (hmH a) hms
        (hqH a) hqs
    refine ⟨LevyStochCalc.Poisson.Compensated.measurable_uncurry_congr hfun.symm hma,
      LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_congr hfun.symm hpa, LevyStochCalc.Poisson.Compensated.sq_int_global_congr hfun.symm hqa, ?_⟩
    rw [LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_fun N hℱ
      (φ := fun (ω : Ω) (s : ℝ) (e : E) => ∑ i ∈ insert a J, H i ω s e) _ _ _ hfun
      hma hpa hqa T]
    filter_upwards [_root_.Prove2MeSourceProof.h_79a6cde54e31b0f9d920e0b6 N ℱ hℱ (hmH a) hms (hpH a) hps (hqH a) hqs hma hpa
      hqa hT, hae] with ω hadd hsum
    rw [hadd, hsum, Finset.sum_insert ha]
end Linear

end LevyStochCalc.Poisson.Compensated


