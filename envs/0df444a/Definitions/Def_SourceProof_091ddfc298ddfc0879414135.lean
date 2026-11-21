-- Prove2me | Definitions.Def_SourceProof_091ddfc298ddfc0879414135
-- name    : SourceProof_091ddfc298ddfc0879414135
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:15:43.932234+00:00
-- url     : https://prove2.me/theorems/7f8f3527-e3f3-4087-9b43-292df329bddf
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.Compensated.tendsto_lintegral_sq_stochasticIntegral_markCut
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SmallJump_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral over a shrinking family of marks

Restricting an admissible integrand to a measurable set of marks keeps it admissible, and by the
Itô–Lévy isometry the `L²` size of its compensated integral is the energy carried by that set.
Along an antitone family of mark sets whose intersection is null, that energy vanishes by
dominated convergence on the intensity, so the compensated integrals tend to `0` in `L²`.

## Main statements

* `LevyStochCalc.Poisson.Compensated.markCut` — an integrand restricted to a set of marks.
* `LevyStochCalc.Poisson.Compensated.tendsto_lintegral_sq_stochasticIntegral_markCut` — the
  compensated integrals over a shrinking family of marks tend to `0` in `L²`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Cut

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end Cut

section Tendsto

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_091ddfc298ddfc0879414135
    (A : ℕ → Set E) (hA : ∀ m, MeasurableSet (A m)) (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto (fun m => ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ (markCut (A m) φ)
        (measurable_markCut h_meas (hA m)) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b h_progMeas) (hA m))
        (fun T' hT' => sq_markCut h_sq (A m) T' hT') T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (𝓝 0) := by
  classical
  set G : Ω → E → ℝ≥0∞ :=
    fun ω e => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂volume with hGdef
  -- each term is the energy carried by `A m`
  have hiso : ∀ m, ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markCut (A m) φ)
        (LevyStochCalc.Poisson.Compensated.measurable_markCut h_meas (hA m)) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b h_progMeas) (hA m))
        (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut h_sq (A m) T' hT') T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ e in A m, G ω e ∂ν ∂P := by
    intro m
    rw [LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markCut (A m) φ)
      (LevyStochCalc.Poisson.Compensated.measurable_markCut h_meas (hA m)) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b h_progMeas) (hA m))
      (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut h_sq (A m) T' hT') T hT]
    exact lintegral_congr fun ω =>
      LevyStochCalc.Poisson.Compensated.lintegral_markCut_eq_setLIntegral φ (hA m) h_meas T ω
  simp_rw [hiso]
  -- the total energy, as a function of the sample point
  have htot : ∀ ω : Ω, ∫⁻ e, G ω e ∂ν
      = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume := by
    intro ω
    have := LevyStochCalc.Poisson.Compensated.lintegral_markCut_eq_setLIntegral (ν := ν) φ MeasurableSet.univ h_meas T ω
    simpa [LevyStochCalc.Poisson.Compensated.markCut] using this.symm
  have htotmeas : Measurable fun ω => ∫⁻ e, G ω e ∂ν := by
    simp_rw [htot]
    exact LevyStochCalc.Poisson.Compensated.measurable_markEnergy (f := fun ω s e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2)
      ((h_meas.nnnorm.coe_nnreal_ennreal).pow_const 2) T
  have htotfin : ∫⁻ ω, (∫⁻ e, G ω e ∂ν) ∂P ≠ ⊤ := by
    simp_rw [htot]
    exact (h_sq T hT).ne
  -- for almost every sample point the mark energy is finite, so the shrinking sets carry none
  have hGmeas : ∀ ω : Ω, Measurable (G ω) := by
    intro ω
    have hcurry : Measurable fun q : E × ℝ => (‖φ ω q.2 q.1‖₊ : ℝ≥0∞) ^ 2 := by
      have := h_meas.comp (measurable_const.prodMk
        (measurable_snd.prodMk measurable_fst) :
          Measurable fun q : E × ℝ => ((ω, q.2, q.1) : Ω × ℝ × E))
      exact (this.nnnorm.coe_nnreal_ennreal).pow_const 2
    exact Measurable.lintegral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) T)) hcurry
  have hindic : ∀ (m : ℕ) (ω : Ω), ∫⁻ e, (A m).indicator (G ω) e ∂ν = ∫⁻ e in A m, G ω e ∂ν :=
    fun m ω => lintegral_indicator (hA m) _
  have hae : ∀ᵐ ω ∂P, Filter.Tendsto (fun m => ∫⁻ e in A m, G ω e ∂ν) Filter.atTop (𝓝 0) := by
    filter_upwards [MeasureTheory.ae_lt_top htotmeas htotfin] with ω hfin
    have hbound : ∀ m, (fun e => (A m).indicator (G ω) e) ≤ᵐ[ν] G ω :=
      fun m => Filter.Eventually.of_forall fun e =>
        Set.indicator_le_self' (fun _ _ => zero_le) e
    have hmeasF : ∀ m, Measurable fun e => (A m).indicator (G ω) e :=
      fun m => (hGmeas ω).indicator (hA m)
    have hlim : ∀ᵐ e ∂ν, Filter.Tendsto
        (fun m => (A m).indicator (G ω) e) Filter.atTop
        (𝓝 ((⋂ m, A m).indicator (G ω) e)) := by
      refine Filter.Eventually.of_forall fun e => ?_
      by_cases he : e ∈ ⋂ m, A m
      · have hall : ∀ m, e ∈ A m := fun m => Set.mem_iInter.mp he m
        simp only [Set.indicator_of_mem he, Set.indicator_of_mem (hall _)]
        exact tendsto_const_nhds
      · obtain ⟨m₀, hm₀⟩ : ∃ m₀, e ∉ A m₀ := by
          by_contra hcon
          push Not at hcon
          exact he (Set.mem_iInter.mpr fun m => hcon m)
        refine tendsto_atTop_of_eventually_const (i₀ := m₀) fun m hm => ?_
        rw [Set.indicator_of_notMem (fun hmem => hm₀ (hanti hm hmem)),
          Set.indicator_of_notMem he]
    have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (F := fun m e => (A m).indicator (G ω) e)
      (f := (⋂ m, A m).indicator (G ω)) (bound := G ω) hmeasF hbound hfin.ne hlim
    rw [lintegral_indicator (MeasurableSet.iInter hA),
      MeasureTheory.setLIntegral_measure_zero _ _ hnull] at hconv
    simpa only [hindic] using hconv
  -- dominated convergence in the sample point
  have hmeasFm : ∀ m, Measurable fun ω => ∫⁻ e in A m, G ω e ∂ν := by
    intro m
    have hrw : (fun ω => ∫⁻ e in A m, G ω e ∂ν)
        = fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖LevyStochCalc.Poisson.Compensated.markCut (A m) φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume := by
      funext ω
      exact (LevyStochCalc.Poisson.Compensated.lintegral_markCut_eq_setLIntegral φ (hA m) h_meas T ω).symm
    rw [hrw]
    exact LevyStochCalc.Poisson.Compensated.measurable_markEnergy
      (f := fun ω s e => (‖LevyStochCalc.Poisson.Compensated.markCut (A m) φ ω s e‖₊ : ℝ≥0∞) ^ 2)
      (((LevyStochCalc.Poisson.Compensated.measurable_markCut h_meas (hA m)).nnnorm.coe_nnreal_ennreal).pow_const 2) T
  have hboundP : ∀ m, (fun ω => ∫⁻ e in A m, G ω e ∂ν) ≤ᵐ[P] fun ω => ∫⁻ e, G ω e ∂ν :=
    fun m => Filter.Eventually.of_forall fun ω =>
      MeasureTheory.setLIntegral_le_lintegral _ _
  have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (F := fun m ω => ∫⁻ e in A m, G ω e ∂ν) (f := fun _ : Ω => (0 : ℝ≥0∞))
    (bound := fun ω => ∫⁻ e, G ω e ∂ν) hmeasFm hboundP htotfin hae
  simpa using hconv
end Tendsto

end LevyStochCalc.Poisson.Compensated


