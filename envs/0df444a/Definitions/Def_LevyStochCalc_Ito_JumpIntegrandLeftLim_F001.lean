-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpIntegrandLeftLim_F001
-- name    : LevyStochCalc_Ito_JumpIntegrandLeftLim_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:21:41.188489+00:00
-- url     : https://prove2.me/theorems/6c6f6940-07a7-4b7a-b8df-9602f760ddfc
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpIntegrandLeftLim
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpIntegrandLeftLim. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_CadlagJumps_F000
import Definitions.Def_LevyStochCalc_Analysis_CadlagJumps_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F000
import Definitions.Def_LevyStochCalc_Poisson_Compensated_F000
import Definitions.Def_SourceProof_27ffb6837c072f81fc480f19
import Definitions.Def_SourceProof_ba87322c9970bc59472f4ba2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrands evaluated along the left limits of a path

A path in `ℝⁿ` that is right continuous on `[0, ∞)` and has left limits at every positive time
meets those left limits off a countable, hence Lebesgue null, set of times. An integrand
evaluated along such a path and the same integrand evaluated along a process that meets the path
at all but countably many positive times therefore agree almost everywhere for the product of the
sample measure, Lebesgue measure on the horizon and the mark measure, so the compensated integral
takes the same value on the two integrands; the same null set serves the iterated integral
against the mark measure and Lebesgue measure and the integral against the reference intensity.

The identification is one of `L²` classes: it concerns the compensated integral constructed from
the energy isometry, not a pathwise Stieltjes integral against the jump measure, for which the
two conventions differ.

## Main statements

* `countable_setOf_pos_ne_of_cadlag` — a path right continuous on `[0, ∞)` differs from its left
  limits at only countably many positive times.
* `compensatedIntegral_congr_of_countable_ne` — the compensated integrals of an integrand
  evaluated along two processes meeting at all but countably many positive times agree almost
  surely.
* `setIntegral_congr_of_countable_ne` and
  `setIntegral_referenceIntensity_congr_of_countable_ne` — the same for the compensator drift
  term, in its iterated and its product-measure form.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito

universe u v w

section Cadlag

variable {n : ℕ}

/-- A path in `ℝⁿ` that is right continuous on `[0, ∞)` meets a process carrying its left limits
at almost every positive time. -/
theorem ae_eq_of_cadlag {f g : ℝ → Fin n → ℝ}
    (hright : ∀ t : ℝ, 0 ≤ t → Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, 0 < t → ∀ i : Fin n,
      Tendsto (fun s => f s i) (𝓝[<] t) (𝓝 (g t i))) :
    ∀ᵐ t ∂(volume : Measure ℝ), 0 < t → f t = g t := by
  rw [ae_iff]
  refine measure_mono_null (fun t ht => ?_)
    ((_root_.Prove2MeSourceProof.h_27ffb6837c072f81fc480f19 hright hleft).measure_zero volume)
  simp only [Set.mem_setOf_eq] at ht ⊢
  have h1 : 0 < t := by
    by_contra hc
    exact ht fun hp => absurd hp hc
  exact ⟨h1, fun heq => ht fun _ => heq⟩
end Cadlag

section Horizon

/-- Almost every time of a horizon starting at the origin is positive. -/
theorem ae_pos_restrict_Icc (T : ℝ) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), 0 < s := by
  have hset : {s : ℝ | ¬ 0 < s} = Set.Iic 0 := by
    ext s
    simp [not_lt]
  have hsub : Set.Iic (0 : ℝ) ∩ Set.Icc (0 : ℝ) T ⊆ {(0 : ℝ)} := by
    intro s hs
    exact Set.mem_singleton_iff.mpr (le_antisymm hs.1 hs.2.1)
  rw [ae_iff, hset, Measure.restrict_apply measurableSet_Iic]
  exact measure_mono_null hsub (measure_singleton 0)
end Horizon

section Integrand

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {V : Type w}
  {P : Measure Ω}

omit [MeasurableSpace Ω] in
/-- A process meets almost every value on a horizon of a second process that it meets at all but
countably many positive times. -/
theorem ae_restrict_eq_of_countable_ne {X Xm : ℝ → Ω → V} {ω : Ω}
    (hω : {s : ℝ | 0 < s ∧ Xm s ω ≠ X s ω}.Countable) (T : ℝ) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Xm s ω = X s ω := by
  have hS : ∀ᵐ s ∂(volume : Measure ℝ), ¬ (0 < s ∧ Xm s ω ≠ X s ω) := by
    rw [ae_iff]
    refine measure_mono_null (fun s hs => ?_) (hω.measure_zero volume)
    simpa using hs
  filter_upwards [ae_pos_restrict_Icc T, ae_restrict_of_ae hS] with s hs1 hs2
  by_contra hne
  exact hs2 ⟨hs1, hne⟩
omit [MeasurableSpace E] in
/-- Almost surely, a marked integrand evaluated along a process and along a second process that
meets it at all but countably many positive times agree at almost every time of a horizon and at
every mark. -/
theorem ae_ae_forall_eq_of_countable_ne {X Xm : ℝ → Ω → V} (F : ℝ → V → E → ℝ)
    (hXm : ∀ᵐ ω ∂P, {s : ℝ | 0 < s ∧ Xm s ω ≠ X s ω}.Countable) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ e : E, F s (Xm s ω) e = F s (X s ω) e := by
  filter_upwards [hXm] with ω hω
  filter_upwards [ae_restrict_eq_of_countable_ne hω T] with s hs
  intro e
  rw [hs]
end Integrand

section Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {V : Type w}
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] in
/-- Two marked integrands that agree at every mark and at almost every time of a horizon, almost
surely, agree almost everywhere for the marked energy measure of that horizon. -/
theorem markedEnergyMeasure_ae_eq_of_ae_ae {φ ψ : Ω → ℝ → E → ℝ}
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hψm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2) (T : ℝ)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ e : E, φ ω s e = ψ ω s e) :
    (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
      =ᵐ[Poisson.Compensated.markedEnergyMeasure P ν T]
        fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2 := by
  have hset : MeasurableSet {p : Ω × ℝ × E | φ p.1 p.2.1 p.2.2 = ψ p.1 p.2.1 p.2.2} :=
    hφm.stronglyMeasurable.measurableSet_eq_fun hψm.stronglyMeasurable
  rw [Poisson.Compensated.markedEnergyMeasure]
  rw [Filter.EventuallyEq, Measure.ae_prod_iff_ae_ae hset]
  filter_upwards [h] with ω hω
  have hset' : MeasurableSet {q : ℝ × E | φ ω q.1 q.2 = ψ ω q.1 q.2} :=
    measurable_prodMk_left hset
  rw [Measure.ae_prod_iff_ae_ae hset']
  filter_upwards [hω] with s hs
  exact ae_of_all _ fun e => hs e
/-- **The compensated integral of a marked integrand evaluated along a process is unchanged when
the process is replaced by one meeting it at all but countably many positive times.** -/
theorem compensatedIntegral_congr_of_countable_ne
    (N : Poisson.PoissonRandomMeasure P ν) (hℱ : Poisson.IsPoissonFiltration N ℱ)
    {X Xm : ℝ → Ω → V} (F : ℝ → V → E → ℝ)
    (hXm : ∀ᵐ ω ∂P, {s : ℝ | 0 < s ∧ Xm s ω ≠ X s ω}.Countable)
    (hmm : Measurable fun p : Ω × ℝ × E => F p.2.1 (Xm p.2.1 p.1) p.2.2)
    (hm : Measurable fun p : Ω × ℝ × E => F p.2.1 (X p.2.1 p.1) p.2.2)
    (hpm : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => F s (Xm s ω) e)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => F s (X s ω) e)
    (hqm : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖F s (Xm s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖F s (X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    Poisson.Compensated.stochasticIntegral N ℱ hℱ (fun ω s e => F s (Xm s ω) e) hmm hpm hqm T
      =ᵐ[P] Poisson.Compensated.stochasticIntegral N ℱ hℱ
        (fun ω s e => F s (X s ω) e) hm hp hq T :=
  _root_.Prove2MeSourceProof.h_ba87322c9970bc59472f4ba2 N hℱ _ _ hmm hm hpm hp hqm hq hT
    (markedEnergyMeasure_ae_eq_of_ae_ae hmm hm T (ae_ae_forall_eq_of_countable_ne F hXm T))
end Compensated

section Drift

variable {Ω : Type u} {E : Type v} [MeasurableSpace E] {V : Type w}

/-- The iterated integral of a marked integrand against the mark measure and Lebesgue measure on
a horizon is unchanged when the process it is evaluated along is replaced by one meeting it at
all but countably many positive times. -/
theorem setIntegral_congr_of_countable_ne {X Xm : ℝ → Ω → V} (F : ℝ → V → E → ℝ)
    (ν : Measure E) {ω : Ω} (hω : {s : ℝ | 0 < s ∧ Xm s ω ≠ X s ω}.Countable) (T : ℝ) :
    (∫ s in Set.Icc (0 : ℝ) T, ∫ e, F s (Xm s ω) e ∂ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e, F s (X s ω) e ∂ν := by
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_eq_of_countable_ne hω T] with s hs
  rw [hs]
/-- The integral of a marked integrand against the reference intensity over a left-open horizon
and a mark set is unchanged when the process it is evaluated along is replaced by one meeting it
at all but countably many positive times. -/
theorem setIntegral_referenceIntensity_congr_of_countable_ne {X Xm : ℝ → Ω → V}
    (F : ℝ → V → E → ℝ) {ν : Measure E} [SigmaFinite ν] {ω : Ω}
    (hω : {s : ℝ | 0 < s ∧ Xm s ω ≠ X s ω}.Countable) {A : Set E} (hA : MeasurableSet A)
    (T : ℝ) :
    (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, F q.1 (Xm q.1 ω) q.2 ∂(Poisson.referenceIntensity ν))
      = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, F q.1 (X q.1 ω) q.2 ∂(Poisson.referenceIntensity ν) := by
  refine integral_congr_ae ?_
  have hR : MeasurableSet (Set.Ioc (0 : ℝ) T ×ˢ A) := measurableSet_Ioc.prod hA
  have hnull : Poisson.referenceIntensity ν
      ({s : ℝ | 0 < s ∧ Xm s ω ≠ X s ω} ×ˢ (Set.univ : Set E)) = 0 := by
    rw [Poisson.referenceIntensity, Measure.prod_prod]
    have h0 : (volume.restrict (Set.Ici (0 : ℝ))) {s : ℝ | 0 < s ∧ Xm s ω ≠ X s ω} = 0 := by
      rw [Measure.restrict_apply hω.measurableSet]
      exact measure_mono_null Set.inter_subset_left (hω.measure_zero volume)
    rw [h0, zero_mul]
  have hout : ∀ᵐ q ∂(Poisson.referenceIntensity ν).restrict (Set.Ioc (0 : ℝ) T ×ˢ A),
      q ∉ {s : ℝ | 0 < s ∧ Xm s ω ≠ X s ω} ×ˢ (Set.univ : Set E) := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    refine measure_mono_null (fun q hq => ?_) hnull
    simpa using hq
  filter_upwards [ae_restrict_mem hR, hout] with q hq1 hq2
  have hne : Xm q.1 ω = X q.1 ω := by
    by_contra hc
    exact hq2 (Set.mem_prod.mpr ⟨⟨hq1.1.1, hc⟩, Set.mem_univ _⟩)
  rw [hne]
end Drift

end LevyStochCalc.Ito


