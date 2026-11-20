-- Prove2me | Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002
-- name    : LevyStochCalc_Probability_DoobContinuous_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T14:57:24.438859+00:00
-- url     : https://prove2.me/theorems/2b93e772-6e39-4135-8923-6811dd7140c6
-- title:
--   Source declarations: LevyStochCalc.Probability.DoobContinuous
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.DoobContinuous. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F001
import Definitions.Def_SourceProof_755d31da2fec92eb2a10cfd6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Doob's `L²` maximal inequality in continuous time

For a right-continuous martingale on `[0, T]`, the supremum of the paths over the window is
square integrable, with `𝔼[sup_{t ≤ T} |M_t|²] ≤ 4 𝔼[|M_T|²]`.

The discrete inequality is `MeasureTheory.Martingale.eLpNorm_norm_runMax_le`; the passage to
continuous time samples the martingale along the dyadic partition of `[0, T]`, whose points are
increasing in the level, and uses right-continuity to identify the supremum over the window with
the supremum of the sampled maxima.

## Main statements

* `Filtration.compMono`, `martingale_compMono` — sampling along a monotone time map.
* `dyadicTime` — the dyadic partition points of `[0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Sampling along a monotone time map -/

/-! ### The dyadic partition of `[0, T]` -/

/-! ### The sampled running maxima -/

variable {M : ℝ → Ω → ℝ} {T : ℝ}

/-! ### The supremum over the window -/

/-! ### Doob's `L²` inequality in continuous time -/

/-- Squaring commutes with the supremum of a monotone sequence. -/
theorem iSup_sq_of_monotone {a : ℕ → ℝ≥0∞} (ha : Monotone a) :
    (⨆ n, a n) ^ 2 = ⨆ n, a n ^ 2 := by
  refine le_antisymm ?_ (iSup_le fun n => pow_le_pow_left' (le_iSup a n) 2)
  rw [pow_two, ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => le_iSup_of_le (max n m) ?_
  rw [pow_two]
  exact mul_le_mul' (ha (le_max_left n m)) (ha (le_max_right n m))
/-- The `L²` seminorm as a `lintegral`. -/
theorem eLpNorm_two_eq {μ : Measure Ω} (f : Ω → ℝ) :
    eLpNorm f 2 μ = (∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.rpow_natCast _ 2]
  norm_num
  simp [enorm_eq_nnnorm]
/-- **Doob's `L²` maximal inequality at a dyadic level.** -/
theorem lintegral_sq_dyadicRunMax_le {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} (hM : MeasureTheory.Martingale M ℱ μ) (hT : 0 ≤ T) (n : ℕ) :
    ∫⁻ ω, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have hsamp := martingale_compMono hM (dyadicTime T n) (dyadicTime_monotone hT n)
  have hdoob := MeasureTheory.Martingale.eLpNorm_norm_runMax_le hsamp
    (by norm_num : (1 : ℝ) < 2) (2 ^ n)
  have hp : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    simp
  have hc : ENNReal.ofReal ((2 : ℝ) / (2 - 1)) = (2 : ℝ≥0∞) := by
    norm_num
  rw [hp, hc, dyadicTime_top n] at hdoob
  have hlhs : eLpNorm (fun ω => (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
      fun k => ‖M (dyadicTime T n k) ω‖) 2 μ = eLpNorm (dyadicRunMax M T n) 2 μ := rfl
  rw [hlhs, eLpNorm_two_eq, eLpNorm_two_eq] at hdoob
  have hsq := ENNReal.rpow_le_rpow hdoob (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.rpow_mul] at hsq
  norm_num at hsq
  calc ∫⁻ ω, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ
      = (∫⁻ ω, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ^ (1 : ℝ) := by
        rw [ENNReal.rpow_one]
    _ ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
        simpa using hsq
/-- **Doob's `L²` inequality over the dyadic points.** No path regularity is needed: the
supremum runs over the countable family of partition points. -/
theorem lintegral_iSup_dyadicRunMax_sq_le {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} (hM : MeasureTheory.Martingale M ℱ μ) (hT : 0 ≤ T) :
    ∫⁻ ω, (⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)) ^ 2 ∂μ
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have hMm : ∀ t : ℝ, Measurable (M t) := fun t => ((hM.1 t).mono (ℱ.le t)).measurable
  have heq : (fun ω => (⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)) ^ 2)
      = fun ω => ⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 :=
    funext fun ω => iSup_sq_of_monotone (enorm_dyadicRunMax_mono M T ω)
  rw [heq, lintegral_iSup (fun n => (measurable_enorm_dyadicRunMax hMm T n).pow_const 2)
    (fun m n hmn ω => pow_le_pow_left' (enorm_dyadicRunMax_mono M T ω hmn) 2)]
  exact iSup_le fun n => lintegral_sq_dyadicRunMax_le hM hT n
/-- **Doob's `L²` maximal inequality in continuous time.** For a right-continuous martingale, the
supremum of the path over `[0, T]` has second moment at most four times that of the terminal
value. -/
theorem lintegral_iSup_sq_le_of_martingale {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} (hM : MeasureTheory.Martingale M ℱ μ) (hT : 0 ≤ T)
    (hcad : ∀ᵐ ω ∂μ, ∀ t : ℝ, Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Ioi t))
      (nhds (M t ω))) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂μ
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have hcongr : ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂μ
      = ∫⁻ ω, (⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hcad] with ω hω
    rw [_root_.Prove2MeSourceProof.h_755d31da2fec92eb2a10cfd6 hT hω]
  rw [hcongr]
  exact lintegral_iSup_dyadicRunMax_sq_le hM hT
/-! ### Bounding the supremum over the window -/

/-- The sampled running maximum is subadditive. -/
theorem enorm_dyadicRunMax_add_le (A B : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
    (‖dyadicRunMax (fun t ω => A t ω + B t ω) T n ω‖₊ : ℝ≥0∞)
      ≤ (‖dyadicRunMax A T n ω‖₊ : ℝ≥0∞) + (‖dyadicRunMax B T n ω‖₊ : ℝ≥0∞) := by
  rw [_root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a, _root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a, _root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a]
  refine iSup_le fun k => ?_
  have hpt : (‖A (dyadicTime T n (k : ℕ)) ω + B (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞)
      ≤ (‖A (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞)
        + (‖B (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) := by
    rw [← ENNReal.coe_add]
    exact ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _)
  exact le_trans hpt (add_le_add
    (le_iSup (fun j : Fin (2 ^ n + 1) => (‖A (dyadicTime T n (j : ℕ)) ω‖₊ : ℝ≥0∞)) k)
    (le_iSup (fun j : Fin (2 ^ n + 1) => (‖B (dyadicTime T n (j : ℕ)) ω‖₊ : ℝ≥0∞)) k))
/-- The supremum of the sampled running maxima is subadditive. -/
theorem iSup_dyadicRunMax_add_le (A B : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    (⨆ n, (‖dyadicRunMax (fun t ω => A t ω + B t ω) T n ω‖₊ : ℝ≥0∞))
      ≤ (⨆ n, (‖dyadicRunMax A T n ω‖₊ : ℝ≥0∞))
        + ⨆ n, (‖dyadicRunMax B T n ω‖₊ : ℝ≥0∞) :=
  iSup_le fun n => le_trans (enorm_dyadicRunMax_add_le A B T n ω)
    (add_le_add (le_iSup (fun m => (‖dyadicRunMax A T m ω‖₊ : ℝ≥0∞)) n)
      (le_iSup (fun m => (‖dyadicRunMax B T m ω‖₊ : ℝ≥0∞)) n))
/-- A pathwise bound over the window bounds the supremum of the sampled running maxima. -/
theorem iSup_dyadicRunMax_le_of_bound {A : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T) {ω : Ω} {c : ℝ≥0∞}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ≤ c) :
    (⨆ n, (‖dyadicRunMax A T n ω‖₊ : ℝ≥0∞)) ≤ c := by
  refine iSup_le fun n => ?_
  rw [_root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a]
  exact iSup_le fun k => h _ (dyadicTime_mem_Icc hT n (k : ℕ))
/-- The supremum over the window of a sum of squared coordinates is bounded by the sum of the
squared coordinatewise suprema. -/
theorem iSup_sum_sq_le {n' : ℕ} (A : ℝ → Ω → (Fin n' → ℝ)) (T : ℝ) (ω : Ω) :
    (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖A (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2)
      ≤ ∑ i, (⨆ t : Set.Icc (0 : ℝ) T, (‖A (t : ℝ) ω i‖₊ : ℝ≥0∞)) ^ 2 := by
  refine iSup_le fun t => Finset.sum_le_sum fun i _ => ?_
  exact pow_le_pow_left' (le_iSup (fun u : Set.Icc (0 : ℝ) T =>
    (‖A (u : ℝ) ω i‖₊ : ℝ≥0∞)) t) 2
/-! ### Finite sums -/

end LevyStochCalc.Probability


