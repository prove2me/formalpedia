-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F001
-- name    : LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:41:57.108022+00:00
-- url     : https://prove2.me/theorems/2e695841-bccd-4ab5-a85f-779368b0bf25
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaUnboundedClamp
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaUnboundedClamp. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F000
import Definitions.Def_SourceProof_017cdf5d7acbcd18b949050e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Coefficients of a vector Itô process clamped at a finite level

Clamping the coefficients of a vector Itô process at level `j` leaves bounded coefficients of
finite energy whose distance in energy to the original coefficients tends to `0`, and the process
they drive stays within that distance of the original one in `L²`, uniformly on a bounded window;
along a suitable subsequence of levels the clamped processes converge to the original one almost
surely.

## Main statements

* `LevyStochCalc.Brownian.Ito.clampCoeff`, `clampDrift` — the clamped coefficients.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_window_clamp` — the mesh of the approximation.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section ClampProcess

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

/-- **The energy of the approximation error over the whole window.** -/
theorem lintegral_window_sq_norm_clampProcess_sub_le
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k))
    (hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (j : ℕ) {T : ℝ} :
    ∫⁻ s in Set.Icc (0 : ℝ) T, (∫⁻ ω,
        (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
            (fun p k => measurable_clampCoeff hm j p k)
            (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
            (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
            X₀ (clampDrift b j) s ω
          - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      ≤ ENNReal.ofReal T * clampMesh P H b T j := by
  have hset : ∫⁻ s in Set.Icc (0 : ℝ) T, (∫⁻ ω,
        (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
            (fun p k => measurable_clampCoeff hm j p k)
            (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
            (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
            X₀ (clampDrift b j) s ω
          - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      = ∫⁻ s in Set.Ioc (0 : ℝ) T, (∫⁻ ω,
        (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
            (fun p k => measurable_clampCoeff hm j p k)
            (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
            (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
            X₀ (clampDrift b j) s ω
          - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume := by
    exact (MeasureTheory.setLIntegral_congr (MeasureTheory.Ioc_ae_eq_Icc)).symm
  rw [hset]
  calc ∫⁻ s in Set.Ioc (0 : ℝ) T, (∫⁻ ω,
        (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
            (fun p k => measurable_clampCoeff hm j p k)
            (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
            (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
            X₀ (clampDrift b j) s ω
          - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      ≤ ∫⁻ _s in Set.Ioc (0 : ℝ) T, clampMesh P H b T j ∂volume := by
        refine MeasureTheory.setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
        exact _root_.Prove2MeSourceProof.h_017cdf5d7acbcd18b949050e W ℱ' hcoord hm hpg hq hX₀ hbm hbq j
          hs.1 hs.2
    _ = ENNReal.ofReal T * clampMesh P H b T j := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
/-- **The `L²` distance between a version and the version of the clamped process**, at a single
time of the window. -/
theorem lintegral_sq_norm_version_clamp_sub_le
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {j : ℕ} {X Xj : ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X)
    (hXj : IsVectorItoVersion W ℱ' hcoord (clampCoeff H j)
      (fun p k => measurable_clampCoeff hm j p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
      X₀ (clampDrift b j) Xj)
    {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T) :
    ∫⁻ ω, (‖Xj s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ clampMesh P H b T j := by
  have hcongr : ∫⁻ ω, (‖Xj s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
            (fun p k => measurable_clampCoeff hm j p k)
            (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
            (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
            X₀ (clampDrift b j) s ω
          - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b s ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hX.ae_eq s hs.le, hXj.ae_eq s hs.le] with ω h1 h2
    rw [h1, h2]
  rw [hcongr]
  exact _root_.Prove2MeSourceProof.h_017cdf5d7acbcd18b949050e W ℱ' hcoord hm hpg hq hX₀ hbm hbq j hs hsT
/-- **The energy of the approximation error of the versions over the whole window.** -/
theorem lintegral_window_sq_norm_version_clamp_sub_le
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {j : ℕ} {X Xj : ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X)
    (hXj : IsVectorItoVersion W ℱ' hcoord (clampCoeff H j)
      (fun p k => measurable_clampCoeff hm j p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
      X₀ (clampDrift b j) Xj)
    {T : ℝ} :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖Xj s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal T * clampMesh P H b T j := by
  have hjoint : Measurable fun q : Ω × ℝ => (‖Xj q.2 q.1 - X q.2 q.1‖₊ : ℝ≥0∞) ^ 2 :=
    (((hXj.measurable_uncurry.sub hX.measurable_uncurry).nnnorm).coe_nnreal_ennreal).pow_const 2
  rw [MeasureTheory.lintegral_lintegral_swap hjoint.aemeasurable]
  have hIoc : ∫⁻ s in Set.Icc (0 : ℝ) T, (∫⁻ ω, (‖Xj s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      = ∫⁻ s in Set.Ioc (0 : ℝ) T, (∫⁻ ω, (‖Xj s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume :=
    (MeasureTheory.setLIntegral_congr (MeasureTheory.Ioc_ae_eq_Icc)).symm
  rw [hIoc]
  calc ∫⁻ s in Set.Ioc (0 : ℝ) T, (∫⁻ ω, (‖Xj s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      ≤ ∫⁻ _s in Set.Ioc (0 : ℝ) T, clampMesh P H b T j ∂volume := by
        refine MeasureTheory.setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
        exact lintegral_sq_norm_version_clamp_sub_le W ℱ' hcoord hX₀ hbm hbq hX hXj hs.1 hs.2
    _ = ENNReal.ofReal T * clampMesh P H b T j := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
/-- If the integrals of a sequence of nonnegative functions are summable, their sum is finite
almost everywhere. -/
theorem ae_tsum_ne_top_of_lintegral_summable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : ℕ → α → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (hsum : ∑' i : ℕ, ∫⁻ a, g i a ∂μ ≠ ⊤) : ∀ᵐ a ∂μ, ∑' i : ℕ, g i a ≠ ⊤ := by
  have h1 : ∫⁻ a, ∑' i : ℕ, g i a ∂μ ≠ ⊤ := by
    rw [MeasureTheory.lintegral_tsum fun i => (hg i).aemeasurable]
    exact hsum
  filter_upwards [MeasureTheory.ae_lt_top (Measurable.tsum hg) h1] with a ha
  exact ha.ne
/-- If the integrals of a sequence of nonnegative functions are summable, the functions tend to
zero almost everywhere. -/
theorem ae_tendsto_zero_of_lintegral_summable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : ℕ → α → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (hsum : ∑' i : ℕ, ∫⁻ a, g i a ∂μ ≠ ⊤) :
    ∀ᵐ a ∂μ, Filter.Tendsto (fun i => g i a) Filter.atTop (𝓝 0) := by
  filter_upwards [ae_tsum_ne_top_of_lintegral_summable hg hsum] with a ha
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha
end ClampProcess

end Clamped

end LevyStochCalc.Brownian.Ito


