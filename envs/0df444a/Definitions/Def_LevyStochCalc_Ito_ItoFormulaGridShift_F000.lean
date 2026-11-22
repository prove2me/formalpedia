-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaGridShift_F000
-- name    : LevyStochCalc_Ito_ItoFormulaGridShift_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:15:01.190465+00:00
-- url     : https://prove2.me/theorems/80155fc7-452f-4a3b-8411-bd653b6725e2
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaGridShift
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaGridShift. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaGeneralShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaGeneralShift_F003
import Definitions.Def_SourceProof_c420c5d06462fb990bdab16f
import Definitions.Def_SourceProof_f726d8526913cd14b0792e3b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula between two stopping times of unrestricted range

A stopping time is approximated from above by the stopping time that stops at the first point of
a uniform grid strictly beyond it, which takes finitely many values below the horizon. Itô's
formula for the increment of a path between two such discretisations, for a `C²` function
translated by a random vector, passes to the limit: the boundary term converges by continuity of
the function and of the path, the two Lebesgue terms converge along almost every path by
domination, and the stochastic term converges in `L²` because the energy of the difference of two
increments is at most twice the sum of the two energies, hence almost surely along a subsequence
common to the finitely many Brownian channels.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurableSpace_le_gridStop` — the σ-algebra of a stopping time is
  contained in that of its upward grid discretisation.
* `LevyStochCalc.Brownian.Ito.tendsto_stopped_gridStop` — the integrand cut off at the grid
  discretisations converges pointwise at every positive time of the window.
* `LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_gridStop` — the Lebesgue terms
  converge along the path.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_stopped_sub_gridStop` — the increments cut off at the
  grid discretisations converge in the energy of the window.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_gridShift` — Itô's formula for the increment of a
  path between two stopping times of unrestricted range.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section GridMeasurableSpace

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The σ-algebra of a stopping time is contained in the σ-algebra of the stopping time that stops
at the first point of a uniform grid strictly beyond it. -/
theorem measurableSpace_le_gridStop {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ) (t : ℝ) (m : ℕ) :
    hσ.measurableSpace ≤ (isStoppingTime_gridStop σ hσ t m).measurableSpace :=
  hσ.measurableSpace_mono _ fun ω => le_gridStop σ t m ω
/-- A mark measurable at a stopping time is measurable at its upward grid discretisation. -/
theorem measurable_gridStop_measurableSpace {α : Type*} [MeasurableSpace α]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ : Ω → WithTop ℝ}
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) {c : Ω → α}
    (hc : Measurable[hσ.measurableSpace] c) (t : ℝ) (m : ℕ) :
    Measurable[(isStoppingTime_gridStop σ hσ t m).measurableSpace] c :=
  hc.mono (measurableSpace_le_gridStop hσ t m) le_rfl
end GridMeasurableSpace

section PointwiseLimit

variable {Ω : Type u}

/-- The integrand cut off at the upward grid discretisations of a stopping time converges to the
integrand cut off at that stopping time, at every positive time of the window. -/
theorem tendsto_stopped_gridStop (υ : Ω → WithTop ℝ) (A : Ω → ℝ → ℝ) (ω : Ω)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t) :
    Filter.Tendsto (fun m : ℕ => Probability.stopped (gridStop υ t m) A ω s) Filter.atTop
      (𝓝 (Probability.stopped υ A ω s)) := by
  by_cases hυ : ((s : ℝ) : WithTop ℝ) ≤ υ ω
  · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun m _ => ?_
    have h1 : ((s : ℝ) : WithTop ℝ) ≤ gridStop υ t m ω := le_trans hυ (le_gridStop υ t m ω)
    simp [Probability.stopped, h1, hυ]
  · rw [not_le] at hυ
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (_root_.Prove2MeSourceProof.h_c420c5d06462fb990bdab16f υ ht ω hs hst hυ)
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun m hmN => ?_
    have h1 : ¬ ((s : ℝ) : WithTop ℝ) ≤ gridStop υ t m ω := not_le.mpr (hN m hmN)
    have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ υ ω := not_le.mpr hυ
    simp [Probability.stopped, h1, h2]
end PointwiseLimit

section LebesgueTerm

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The increment between the upward grid discretisations of two stopping times of an integrand
dominated by a multiple of an integrable coefficient converges on a bounded half-open window. -/
theorem tendsto_setIntegral_stopped_sub_gridStop {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {A : Ω → ℝ → ℝ}
    (hmA : Measurable (Function.uncurry A)) (D : Ω → ℝ → ℝ) (K : ℝ)
    (hAD : ∀ ω s, |A ω s| ≤ K * |D ω s|) {t : ℝ} (ht : 0 < t) {ω : Ω}
    (hint : MeasureTheory.IntegrableOn (fun s => D ω s) (Set.Ioc (0 : ℝ) t) volume) :
    Filter.Tendsto (fun m : ℕ => ∫ s in Set.Ioc (0 : ℝ) t,
        (Probability.stopped (gridStop τ t m) A ω s
          - Probability.stopped (gridStop σ t m) A ω s) ∂volume)
      Filter.atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ) t,
        (Probability.stopped τ A ω s - Probability.stopped σ A ω s) ∂volume)) := by
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun s => 2 * (K * |D ω s|)) (fun m => ?_) ((hint.abs.const_mul K).const_mul 2)
    (fun m => ?_) ?_
  · exact (Measurable.of_uncurry_left (measurable_uncurry_stopped_sub
      (isStoppingTime_gridStop σ hσ t m) (isStoppingTime_gridStop τ hτ t m)
      hmA)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    refine le_trans (abs_stopped_sub_stopped_le _ _ A ω s) ?_
    exact mul_le_mul_of_nonneg_left (hAD ω s) (by norm_num)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    exact (tendsto_stopped_gridStop τ A ω ht hs.1 hs.2).sub
      (tendsto_stopped_gridStop σ A ω ht hs.1 hs.2)
end LebesgueTerm

section EnergyTerm

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- An integrand whose square is dominated pointwise by twice the sum of the squares of two others
has energy at most twice the sum of their energies. -/
theorem lintegral_energy_le_two_mul (K H₁ H₂ : Ω → ℝ → ℝ)
    (hbound : ∀ ω s, (‖K ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2)
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂)) (T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      ≤ 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have e1 := measurable_energyDensity hm₁ T
  have e2 := measurable_energyDensity hm₂ T
  rw [← lintegral_const_mul 2 e1, ← lintegral_const_mul 2 e2,
    ← lintegral_add_left (e1.const_mul 2)]
  refine lintegral_mono fun ω => ?_
  have h1 : Measurable fun s => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 :=
    (((measurable_nnnorm.comp (hm₁.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
  have h2 : Measurable fun s => (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 :=
    (((measurable_nnnorm.comp (hm₂.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
  rw [← lintegral_const_mul 2 h1, ← lintegral_const_mul 2 h2,
    ← lintegral_add_left (h1.const_mul 2)]
  exact lintegral_mono fun s => hbound ω s
/-- The increments cut off at the upward grid discretisations of two stopping times converge, in
the energy of the window, to the increment cut off at those stopping times. -/
theorem tendsto_energy_stopped_sub_gridStop {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {G : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry G)) {t : ℝ} (ht : 0 < t)
    (hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Filter.Tendsto (fun m : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖(Probability.stopped (gridStop τ t m) G ω s
              - Probability.stopped (gridStop σ t m) G ω s)
            - (Probability.stopped τ G ω s - Probability.stopped σ G ω s)‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P) Filter.atTop (𝓝 0) := by
  have hEτ := _root_.Prove2MeSourceProof.h_f726d8526913cd14b0792e3b hτ hm ht hq
  have hEσ := _root_.Prove2MeSourceProof.h_f726d8526913cd14b0792e3b hσ hm ht hq
  have hub : Filter.Tendsto (fun m : ℕ =>
      2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖Probability.stopped (gridStop τ t m) G ω s
            - Probability.stopped τ G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖Probability.stopped (gridStop σ t m) G ω s
              - Probability.stopped σ G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hEτ (Or.inr (by simp))
    have h2 := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hEσ (Or.inr (by simp))
    rw [mul_zero] at h1 h2
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
    (fun _ => zero_le) fun m => ?_
  refine lintegral_energy_le_two_mul
    (fun ω s => (Probability.stopped (gridStop τ t m) G ω s
        - Probability.stopped (gridStop σ t m) G ω s)
      - (Probability.stopped τ G ω s - Probability.stopped σ G ω s))
    (fun ω s => Probability.stopped (gridStop τ t m) G ω s - Probability.stopped τ G ω s)
    (fun ω s => Probability.stopped (gridStop σ t m) G ω s - Probability.stopped σ G ω s)
    (fun ω s => ?_) ?_ ?_ t
  · rw [show (Probability.stopped (gridStop τ t m) G ω s
          - Probability.stopped (gridStop σ t m) G ω s)
        - (Probability.stopped τ G ω s - Probability.stopped σ G ω s)
      = (Probability.stopped (gridStop τ t m) G ω s - Probability.stopped τ G ω s)
        - (Probability.stopped (gridStop σ t m) G ω s
            - Probability.stopped σ G ω s) from by ring]
    exact le_trans (sq_nnnorm_sub_le_two_mul _ _) (le_of_eq (by ring))
  · exact (Probability.measurable_uncurry_stopped (isStoppingTime_gridStop τ hτ t m) hm).sub
      (Probability.measurable_uncurry_stopped hτ hm)
  · exact (Probability.measurable_uncurry_stopped (isStoppingTime_gridStop σ hσ t m) hm).sub
      (Probability.measurable_uncurry_stopped hσ hm)
end EnergyTerm

section GridShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end GridShift

end LevyStochCalc.Brownian.Ito


