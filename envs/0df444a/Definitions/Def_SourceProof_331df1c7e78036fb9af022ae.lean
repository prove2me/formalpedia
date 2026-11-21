-- Prove2me | Definitions.Def_SourceProof_331df1c7e78036fb9af022ae
-- name    : SourceProof_331df1c7e78036fb9af022ae
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:13:12.811723+00:00
-- url     : https://prove2.me/theorems/d02ae036-b654-4673-be94-ad9e9c89dadb
-- title:
--   LevyStochCalc source module: SourceProof_331df1c7e78036fb9af022ae
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le` comes from the `LevyStochCalc.Brownian.ItoLocality` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_c420c5d06462fb990bdab16f
import Definitions.Def_SourceProof_e0bce38e6a65980ddb5abfb5

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The local property of the Itô integral

Cutting the integrand off at a stopping time `τ` does not change the integral at a time the
stopping time has not yet reached. The stopping time is approximated from above by the
finite-range stopping times that stop at the first point of a uniform grid strictly beyond it,
for which the finite-range optional stopping identity applies directly; the approximation
converges in energy, and an `L²` squeeze removes the approximation.

## Main statements

* `LevyStochCalc.Brownian.Ito.stepStop`, `gridStop` — the two-valued and the grid stopping times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le` — the local property.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos` — the integral to a
  positive time sees the integrand only at positive times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le` — two integrands agreeing
  up to a stopping time have the same integral where that time has not been reached.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)

section GridStop

end GridStop

section Local

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_331df1c7e78036fb9af022ae
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H)
          (Probability.measurable_uncurry_stopped hτ hm)
          (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ hp)
          (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H ω s) hq) t ω
        = stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω := by
  classical
  -- the cut integrand and its approximations
  have hmS := LevyStochCalc.Probability.measurable_uncurry_stopped hτ hm
  have hpS := _root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ hp
  have hqS := LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P) (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ H ω s) hq
  have hmG : ∀ n : ℕ, Measurable (Function.uncurry
      (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H)) :=
    fun n => LevyStochCalc.Probability.measurable_uncurry_stopped (LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop τ hτ t n) hm
  have hpG : ∀ n : ℕ, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H) :=
    fun n => _root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e (LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop τ hτ t n) hp
  have hqG : ∀ (n : ℕ) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun n => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P)
      (fun ω s => LevyStochCalc.Probability.abs_stopped_le (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s) hq
  -- the event on which the stopping time has not been reached
  set A : Set Ω := {ω | ((t : ℝ) : WithTop ℝ) ≤ τ ω} with hAdef
  have hAmeas : MeasurableSet A := by
    have hcompl : A = {ω | τ ω < ((t : ℝ) : WithTop ℝ)}ᶜ := by
      ext ω
      simp only [hAdef, Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    rw [hcompl]
    exact (ℱ.le t _ (hτ.measurableSet_lt t)).compl
  -- on that event the approximations already agree with the uncut integral
  have hagree : ∀ n : ℕ, n ≠ 0 → ∀ᵐ ω ∂P, ω ∈ A →
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H)
          (hmG n) (hpG n) (hqG n) t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω := by
    intro n hn
    have hid := _root_.Prove2MeSourceProof.h_e0bce38e6a65980ddb5abfb5 (LevyStochCalc.Brownian.Ito.gridStop τ t n) W ℱ hℱ
      (LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop τ hτ t n) hm hp hq ht
      ((Finset.range n).image (LevyStochCalc.Brownian.Ito.gridPt t n))
      (by
        intro c hc
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
        exact LevyStochCalc.Brownian.Ito.gridPt_nonneg ht.le n k)
      (by
        intro c hc
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
        exact LevyStochCalc.Brownian.Ito.gridPt_lt_of_lt ht (Finset.mem_range.mp hk))
      (LevyStochCalc.Brownian.Ito.gridStop_finiteRange τ hn)
    filter_upwards [hid] with ω hω hωA
    rw [hω]
    have hzero : ∀ c ∈ (Finset.range n).image (LevyStochCalc.Brownian.Ito.gridPt t n),
        LevyStochCalc.Brownian.Ito.hitInd (LevyStochCalc.Brownian.Ito.gridStop τ t n) c ω = 0 := by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
      have hlt : LevyStochCalc.Brownian.Ito.gridPt t n k < t := LevyStochCalc.Brownian.Ito.gridPt_lt_of_lt ht (Finset.mem_range.mp hk)
      have hne : LevyStochCalc.Brownian.Ito.gridStop τ t n ω ≠ ((LevyStochCalc.Brownian.Ito.gridPt t n k : ℝ) : WithTop ℝ) := by
        intro hcon
        have h1 : ((t : ℝ) : WithTop ℝ) ≤ ((LevyStochCalc.Brownian.Ito.gridPt t n k : ℝ) : WithTop ℝ) :=
          le_trans hωA (le_trans (LevyStochCalc.Brownian.Ito.le_gridStop τ t n ω) (le_of_eq hcon))
        exact absurd (by exact_mod_cast h1 : t ≤ gridPt t n k) (not_le.mpr hlt)
      simp [LevyStochCalc.Brownian.Ito.hitInd, Set.indicator_of_notMem (show ω ∉ {ω | LevyStochCalc.Brownian.Ito.gridStop τ t n ω
        = ((LevyStochCalc.Brownian.Ito.gridPt t n k : ℝ) : WithTop ℝ)} from hne)]
    have hsum : ∑ c ∈ (Finset.range n).image (LevyStochCalc.Brownian.Ito.gridPt t n),
        LevyStochCalc.Brownian.Ito.hitInd (LevyStochCalc.Brownian.Ito.gridStop τ t n) c ω
          * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq c ω) = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [hzero c hc, zero_mul]
    rw [hsum, sub_zero]
  -- the approximations converge to the cut integrand in energy
  have hEtend : Filter.Tendsto (fun n : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
        - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) := by
    have hbmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := LevyStochCalc.Brownian.Ito.measurable_energyDensity hm t
    have hFmeas : ∀ n : ℕ, Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
      fun n => LevyStochCalc.Brownian.Ito.measurable_energyDensity ((hmG n).sub hmS) t
    have hptw : ∀ (n : ℕ) (ω : Ω) (s : ℝ),
        (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
      intro n ω s
      have habs : |LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s - LevyStochCalc.Probability.stopped τ H ω s|
          ≤ |H ω s| := by
        rw [LevyStochCalc.Probability.stopped, LevyStochCalc.Probability.stopped]
        by_cases h1 : ((s : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t n ω
        · by_cases h2 : ((s : ℝ) : WithTop ℝ) ≤ τ ω
          · simp [h1, h2]
          · simp [h1, h2]
        · have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := fun hcon =>
            h1 (le_trans hcon (LevyStochCalc.Brownian.Ito.le_gridStop τ t n ω))
          simp [h1, h2]
      have hle : (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ≤ (‖H ω s‖₊ : ℝ≥0∞) := by
        refine ENNReal.coe_le_coe.mpr ?_
        rw [← NNReal.coe_le_coe]
        simpa [Real.norm_eq_abs] using habs
      gcongr
    have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun n : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) Filter.atTop (𝓝 0) := by
      filter_upwards [MeasureTheory.ae_lt_top hbmeas (hq t ht).ne] with ω hfin
      have hlims : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
          Filter.Tendsto (fun n : ℕ =>
            (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
              - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2) Filter.atTop (𝓝 0) := by
        have hnull : (volume.restrict (Set.Icc (0 : ℝ) t)) {(0 : ℝ)} = 0 := by
          simp
        filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull,
          MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs0 hsmem
        have hsne : s ≠ 0 := by simpa using hs0
        have hs : 0 < s := lt_of_le_of_ne hsmem.1 (Ne.symm hsne)
        by_cases hτs : ((s : ℝ) : WithTop ℝ) ≤ τ ω
        · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun n _ => ?_
          have h1 : ((s : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t n ω :=
            le_trans hτs (LevyStochCalc.Brownian.Ito.le_gridStop τ t n ω)
          simp [LevyStochCalc.Probability.stopped, h1, hτs]
        · rw [not_le] at hτs
          obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
            (_root_.Prove2MeSourceProof.h_c420c5d06462fb990bdab16f τ ht ω hs hsmem.2 hτs)
          refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
          have h1 : ¬ ((s : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t n ω := not_le.mpr (hN n hn)
          have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := not_le.mpr hτs
          simp [LevyStochCalc.Probability.stopped, h1, h2]
      have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
        (μ := volume.restrict (Set.Icc (0 : ℝ) t))
        (F := fun n s => (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2)
        (f := fun _ : ℝ => (0 : ℝ≥0∞))
        (bound := fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2)
        (fun n => ((((hmG n).sub hmS).comp measurable_prodMk_left).nnnorm.coe_nnreal_ennreal
          ).pow_const 2)
        (fun n => Filter.Eventually.of_forall fun s => hptw n ω s) hfin.ne hlims
      simpa using hconv
    have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (F := fun n ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      (f := fun _ : Ω => (0 : ℝ≥0∞))
      (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      hFmeas
      (fun n => Filter.Eventually.of_forall fun ω =>
        lintegral_mono fun s => hptw n ω s)
      (hq t ht).ne hinner
    simpa using hconv
  -- the squeeze
  set D : Ω → ℝ≥0∞ := fun ω => A.indicator (fun ω =>
    (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Probability.stopped τ H) hmS hpS hqS t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2) ω with hDdef
  have hSImeas : ∀ {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K))
      (hpK : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K)
      (hqK : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK t) := by
    intro K hmK hpK hqK
    exact ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ K hmK hpK hqK t).mono
      (ℱ.le t)).measurable
  have hDmeas : Measurable D := by
    refine Measurable.indicator ?_ hAmeas
    exact ((((hSImeas hmS hpS hqS).sub (hSImeas hm hp hq)).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hDle : ∀ n : ℕ, n ≠ 0 → ∫⁻ ω, D ω ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H ω s
          - LevyStochCalc.Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    intro n hn
    rw [← _root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ
      (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) H) (LevyStochCalc.Probability.stopped τ H)
      (hmG n) hmS (hpG n) hpS (hqG n) hqS ht]
    refine lintegral_mono_ae ?_
    filter_upwards [hagree n hn] with ω hω
    by_cases hωA : ω ∈ A
    · simp only [hDdef]
      have hrev : ∀ x y : ℝ, ‖x - y‖₊ = ‖y - x‖₊ := by
        intro x y
        rw [← NNReal.coe_inj]
        simpa using norm_sub_rev x y
      rw [Set.indicator_of_mem hωA, hω hωA, hrev]
    · simp only [hDdef]
      rw [Set.indicator_of_notMem hωA]
      exact zero_le
  have hDzero : ∫⁻ ω, D ω ∂P = 0 := by
    refine le_antisymm ?_ zero_le
    refine ge_of_tendsto hEtend ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact hDle n hn.ne'
  have hDae := (MeasureTheory.lintegral_eq_zero_iff hDmeas).mp hDzero
  filter_upwards [hDae] with ω hω hωA
  have h0 : D ω = 0 := hω
  simp only [hDdef] at h0
  rw [Set.indicator_of_mem (show ω ∈ A from hωA)] at h0
  have hnn : (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Probability.stopped τ H) hmS hpS hqS t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa [pow_eq_zero_iff] using h0
  have : ‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Probability.stopped τ H) hmS hpS hqS t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω‖₊ = 0 := by
    exact_mod_cast hnn
  have hsub : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (LevyStochCalc.Probability.stopped τ H) hmS hpS hqS t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω = 0 := by
    simpa using this
  linarith [hsub]
end Local

end LevyStochCalc.Brownian.Ito


