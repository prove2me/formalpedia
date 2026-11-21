-- Prove2me | Definitions.Def_SourceProof_d125007308283836842bb087
-- name    : SourceProof_d125007308283836842bb087
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:12:35.939221+00:00
-- url     : https://prove2.me/theorems/54c3fe4c-adb1-469b-8842-d93b14c2e231
-- title:
--   LevyStochCalc source module: SourceProof_d125007308283836842bb087
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stochasticIntegral_markedStopped_eq_of_le` comes from the `LevyStochCalc.Ito.CompensatedLocalityStopping` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F001
import Definitions.Def_SourceProof_68dd6350f3aeefa2416beba6
import Definitions.Def_SourceProof_a108b20c3c7f7ed49b14b48f
import Definitions.Def_SourceProof_c420c5d06462fb990bdab16f
import Definitions.Def_SourceProof_df70248aed5926ac78d4f250

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

theorem _root_.Prove2MeSourceProof.h_d125007308283836842bb087 (hτ : IsStoppingTime ℱ τ) {t : ℝ}
    (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegral N ℱ hℱ (markedStopped τ φ) (_root_.Prove2MeSourceProof.h_68dd6350f3aeefa2416beba6 hτ hm)
          (_root_.Prove2MeSourceProof.h_a108b20c3c7f7ed49b14b48f hτ hp) (sq_int_global_markedStopped hq)
          t ω
        = stochasticIntegral N ℱ hℱ φ hm hp hq t ω := by
  classical
  -- the cut integrand and its approximations
  have hmS := _root_.Prove2MeSourceProof.h_68dd6350f3aeefa2416beba6 hτ hm
  have hpS := _root_.Prove2MeSourceProof.h_a108b20c3c7f7ed49b14b48f hτ hp
  have hqS := LevyStochCalc.Poisson.Compensated.sq_int_global_markedStopped (τ := τ) hq
  have hmG : ∀ n : ℕ, Measurable fun p : Ω × ℝ × E =>
      LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ p.1 p.2.1 p.2.2 :=
    fun n => _root_.Prove2MeSourceProof.h_68dd6350f3aeefa2416beba6 (LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop τ hτ t n) hm
  have hpG : ∀ n : ℕ, LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      (LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ) :=
    fun n => _root_.Prove2MeSourceProof.h_a108b20c3c7f7ed49b14b48f (LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop τ hτ t n) hp
  have hqG : ∀ (n : ℕ) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun n => LevyStochCalc.Poisson.Compensated.sq_int_global_markedStopped (τ := LevyStochCalc.Brownian.Ito.gridStop τ t n) hq
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
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ) (hmG n) (hpG n) (hqG n)
          t ω
        = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t ω := by
    intro n hn
    have hid := _root_.Prove2MeSourceProof.h_df70248aed5926ac78d4f250 N hℱ hm hp hq
      (LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop τ hτ t n) ht ((Finset.range n).image (LevyStochCalc.Brownian.Ito.gridPt t n))
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
          * (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t ω
            - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq c ω) = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [hzero c hc, zero_mul]
    rw [hsum, sub_zero]
  -- the approximations converge to the cut integrand in energy
  have hEtend : Filter.Tendsto (fun n : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
      (‖LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ ω s e - LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P) Filter.atTop (𝓝 0) := by
    have hbmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume :=
      LevyStochCalc.Poisson.Compensated.measurable_markedDensity (ν := ν) (φ := φ) hm t
    have hFmeas : ∀ n : ℕ, Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ ω s e - LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume :=
      fun n => LevyStochCalc.Poisson.Compensated.measurable_markedDensity (ν := ν)
        (φ := fun ω s e => LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ ω s e - LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e)
        ((hmG n).sub hmS) t
    have hptw : ∀ (n : ℕ) (ω : Ω) (s : ℝ) (e : E),
        (‖LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ ω s e - LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
          ≤ (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 := by
      intro n ω s e
      have habs : |LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ ω s e - LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e|
          ≤ |φ ω s e| := by
        rw [LevyStochCalc.Poisson.Compensated.markedStopped, LevyStochCalc.Poisson.Compensated.markedStopped]
        by_cases h1 : ((s : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t n ω
        · by_cases h2 : ((s : ℝ) : WithTop ℝ) ≤ τ ω
          · simp [h1, h2]
          · simp [h1, h2]
        · have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := fun hcon =>
            h1 (le_trans hcon (LevyStochCalc.Brownian.Ito.le_gridStop τ t n ω))
          simp [h1, h2]
      have hle : (‖LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ ω s e - LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e‖₊ : ℝ≥0∞)
          ≤ (‖φ ω s e‖₊ : ℝ≥0∞) := by
        refine ENNReal.coe_le_coe.mpr ?_
        rw [← NNReal.coe_le_coe]
        simpa [Real.norm_eq_abs] using habs
      gcongr
    have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun n : ℕ =>
        ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ ω s e - LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume) Filter.atTop (𝓝 0) := by
      filter_upwards [MeasureTheory.ae_lt_top hbmeas (hq t ht).ne] with ω hfin
      have hlims : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
          Filter.Tendsto (fun n : ℕ => ∫⁻ e,
            (‖LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ ω s e - LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
              ∂ν) Filter.atTop (𝓝 0) := by
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
          simp [LevyStochCalc.Poisson.Compensated.markedStopped, h1, hτs]
        · rw [not_le] at hτs
          obtain ⟨N', hN'⟩ := Filter.eventually_atTop.mp
            (_root_.Prove2MeSourceProof.h_c420c5d06462fb990bdab16f τ ht ω hs hsmem.2 hτs)
          refine tendsto_atTop_of_eventually_const (i₀ := N') fun n hn => ?_
          have h1 : ¬ ((s : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t n ω := not_le.mpr (hN' n hn)
          have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := not_le.mpr hτs
          simp [LevyStochCalc.Poisson.Compensated.markedStopped, h1, h2]
      have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
        (μ := volume.restrict (Set.Icc (0 : ℝ) t))
        (F := fun n s => ∫⁻ e,
          (‖LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ ω s e - LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        (f := fun _ : ℝ => (0 : ℝ≥0∞))
        (bound := fun s => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        (fun n => LevyStochCalc.Poisson.Compensated.measurable_markSlice (ν := ν)
          (φ := fun ω s e =>
            LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ ω s e - LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e)
          ((hmG n).sub hmS) ω)
        (fun n => Filter.Eventually.of_forall fun s => lintegral_mono fun e => hptw n ω s e)
        hfin.ne hlims
      simpa using hconv
    have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (F := fun n ω => ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ ω s e - LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume)
      (f := fun _ : Ω => (0 : ℝ≥0∞))
      (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
      hFmeas
      (fun n => Filter.Eventually.of_forall fun ω =>
        lintegral_mono fun s => lintegral_mono fun e => hptw n ω s e)
      (hq t ht).ne hinner
    simpa using hconv
  -- the squeeze
  set D : Ω → ℝ≥0∞ := fun ω => A.indicator (fun ω =>
    (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markedStopped τ φ) hmS hpS hqS t ω
      - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2) ω with hDdef
  have hDmeas : AEMeasurable D P := by
    refine AEMeasurable.indicator ?_ hAmeas
    have h1 := (LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markedStopped τ φ) hmS hpS hqS t
      ).aestronglyMeasurable.aemeasurable
    have h2 := (LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ φ hm hp hq t).aestronglyMeasurable.aemeasurable
    exact (((h1.sub h2).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hDle : ∀ n : ℕ, n ≠ 0 → ∫⁻ ω, D ω ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ ω s e - LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P := by
    intro n hn
    rw [← LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markedStopped (LevyStochCalc.Brownian.Ito.gridStop τ t n) φ)
      (LevyStochCalc.Poisson.Compensated.markedStopped τ φ) (hmG n) hmS (hpG n) hpS (hqG n) hqS t ht]
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
  have hDae := (MeasureTheory.lintegral_eq_zero_iff' hDmeas).mp hDzero
  filter_upwards [hDae] with ω hω hωA
  have h0 : D ω = 0 := hω
  simp only [hDdef] at h0
  rw [Set.indicator_of_mem (show ω ∈ A from hωA)] at h0
  have hnn : (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markedStopped τ φ) hmS hpS hqS t ω
      - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa [pow_eq_zero_iff] using h0
  have : ‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markedStopped τ φ) hmS hpS hqS t ω
      - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t ω‖₊ = 0 := by
    exact_mod_cast hnn
  have hsub : LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markedStopped τ φ) hmS hpS hqS t ω
      - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t ω = 0 := by
    simpa using this
  linarith [hsub]
end Local

end LevyStochCalc.Poisson.Compensated


