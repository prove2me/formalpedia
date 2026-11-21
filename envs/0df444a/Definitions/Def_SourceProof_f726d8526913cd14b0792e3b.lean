-- Prove2me | Definitions.Def_SourceProof_f726d8526913cd14b0792e3b
-- name    : SourceProof_f726d8526913cd14b0792e3b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:12:12.913562+00:00
-- url     : https://prove2.me/theorems/6a942ac2-f02d-47a6-9ff4-d4cb7073ee27
-- title:
--   LevyStochCalc source module: SourceProof_f726d8526913cd14b0792e3b
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.tendsto_energy_stopped_gridStop` comes from the `LevyStochCalc.Ito.ItoFormulaStoppedLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaStopped_F000
import Definitions.Def_SourceProof_c420c5d06462fb990bdab16f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula along a path stopped at an arbitrary stopping time

A stopping time is approximated from above by the stopping times that stop at the first point of
a uniform grid strictly beyond it, which take finitely many values. The horizons clipped at the
approximations converge to the horizon clipped at the stopping time, the integrands cut off at the
approximations converge in the energy of a window to the integrand cut off at the stopping time,
and Itô's formula along the finite-range stopped paths passes to the limit.

## Main statements

* `LevyStochCalc.Brownian.Ito.tendsto_clipTime_gridStop` — the clipped horizons converge.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_stopped_gridStop` — the cut-off integrands converge
  in the energy of the window.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped_general` — the process stopped at a
  stopping time is the vector Itô process of the stopped coefficients.
* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_general` — Itô's formula along the stopped path.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section ClipLimit

variable {Ω : Type u}

end ClipLimit

section Energy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_f726d8526913cd14b0792e3b {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) {t : ℝ} (ht : 0 < t)
    (hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Filter.Tendsto (fun m : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStop τ t m) H ω s
          - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) := by
  have hmS : Measurable (Function.uncurry (LevyStochCalc.Probability.stopped τ H)) :=
    LevyStochCalc.Probability.measurable_uncurry_stopped hτ hm
  have hmG : ∀ m : ℕ, Measurable (Function.uncurry (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) H)) :=
    fun m => LevyStochCalc.Probability.measurable_uncurry_stopped (LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop τ hτ t m) hm
  have hptw : ∀ (m : ℕ) (ω : Ω) (s : ℝ),
      (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) H ω s
        - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro m ω s
    have habs : |LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) H ω s - LevyStochCalc.Probability.stopped τ H ω s|
        ≤ |H ω s| := by
      rw [LevyStochCalc.Probability.stopped, LevyStochCalc.Probability.stopped]
      by_cases h1 : ((s : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t m ω
      · by_cases h2 : ((s : ℝ) : WithTop ℝ) ≤ τ ω
        · simp [h1, h2]
        · simp [h1, h2]
      · have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := fun hcon =>
          h1 (le_trans hcon (LevyStochCalc.Brownian.Ito.le_gridStop τ t m ω))
        simp [h1, h2]
    have hle : (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) H ω s
        - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ≤ (‖H ω s‖₊ : ℝ≥0∞) := by
      refine ENNReal.coe_le_coe.mpr ?_
      rw [← NNReal.coe_le_coe]
      simpa [Real.norm_eq_abs] using habs
    gcongr
  have hbmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := LevyStochCalc.Brownian.Ito.measurable_energyDensity hm t
  have hFmeas : ∀ m : ℕ, Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) H ω s
        - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun m => LevyStochCalc.Brownian.Ito.measurable_energyDensity ((hmG m).sub hmS) t
  have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun m : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) H ω s
        - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) Filter.atTop (𝓝 0) := by
    filter_upwards [MeasureTheory.ae_lt_top hbmeas hq.ne] with ω hfin
    have hlims : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
        Filter.Tendsto (fun m : ℕ =>
          (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) H ω s
            - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2) Filter.atTop (𝓝 0) := by
      have hnull : (volume.restrict (Set.Icc (0 : ℝ) t)) {(0 : ℝ)} = 0 := by simp
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull,
        MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs0 hsmem
      have hsne : s ≠ 0 := by simpa using hs0
      have hs : 0 < s := lt_of_le_of_ne hsmem.1 (Ne.symm hsne)
      by_cases hτs : ((s : ℝ) : WithTop ℝ) ≤ τ ω
      · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun m _ => ?_
        have h1 : ((s : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t m ω :=
          le_trans hτs (LevyStochCalc.Brownian.Ito.le_gridStop τ t m ω)
        simp [LevyStochCalc.Probability.stopped, h1, hτs]
      · rw [not_le] at hτs
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
          (_root_.Prove2MeSourceProof.h_c420c5d06462fb990bdab16f τ ht ω hs hsmem.2 hτs)
        refine tendsto_atTop_of_eventually_const (i₀ := N) fun m hmN => ?_
        have h1 : ¬ ((s : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t m ω := not_le.mpr (hN m hmN)
        have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := not_le.mpr hτs
        simp [LevyStochCalc.Probability.stopped, h1, h2]
    have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (μ := volume.restrict (Set.Icc (0 : ℝ) t))
      (F := fun m s => (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) H ω s
        - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2)
      (f := fun _ : ℝ => (0 : ℝ≥0∞))
      (bound := fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2)
      (fun m => ((((hmG m).sub hmS).comp measurable_prodMk_left).nnnorm.coe_nnreal_ennreal
        ).pow_const 2)
      (fun m => Filter.Eventually.of_forall fun s => hptw m ω s) hfin.ne hlims
    simpa using hconv
  have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (F := fun m ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) H ω s
        - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    (f := fun _ : Ω => (0 : ℝ≥0∞))
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    hFmeas
    (fun m => Filter.Eventually.of_forall fun ω => lintegral_mono fun s => hptw m ω s)
    hq.ne hinner
  simpa using hconv
end Energy

section StoppedGeneral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end StoppedGeneral

end LevyStochCalc.Brownian.Ito


