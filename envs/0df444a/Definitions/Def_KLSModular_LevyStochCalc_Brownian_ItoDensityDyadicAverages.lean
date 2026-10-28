-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoDensityDyadicAverages
-- name    : KLSModular_LevyStochCalc_Brownian_ItoDensityDyadicAverages
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:54:27.75397+00:00
-- url     : https://prove2.me/theorems/0b508cbb-d331-4203-8be8-f69491695e96
-- title:
--   L² truncation and dyadic averaging for Brownian integrands
-- statement:
--   Vendored from LevyStochCalc, repository https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. The truncation results state that clipping a real value at ±M gives a squared error dominated by its squared norm and that, for a jointly measurable H with finite ℝ≥0∞-valued squared lower integral over Ω × [0,T], the clipped error tends to zero as M tends to infinity. `dyadicPartition_brownian` defines the level-n partition of [0,T] with points iT/2ⁿ, and the accompanying lemmas establish its initial value, final value, strict monotonicity for T > 0, interval length, and upper bound by T. `dyadicAvg_brownian` is the normalized integral average of g over each dyadic cell; it is measurable in ω and bounded by M whenever |g ω s| ≤ M. The bundle also includes the ENNReal quadratic triangle bound `sq_nnnorm_add_le_two_mul_brownian`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoSimple
--   import LevyStochCalc.Probability.Progressive
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def dyadicPartition_brownian (T : ℝ) (n : ℕ) :
--       Fin (2 ^ n + 1) → ℝ :=
--     fun i => (i : ℝ) * T / (2 ^ n : ℕ)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoSimple`](https://prove2.me/theorems/795b2ad2-44ee-43f5-a5ba-483135ae893d), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoDensityDyadicAverages.lean) · `LevyStochCalc.Brownian.ItoDensityDyadicAverages` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoDensityDyadicAverages.lean#L28-L356 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoDensityDyadicAverages`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoDensityDyadicAverages`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoSimple
import Definitions.Def_KLSModular_LevyStochCalc_Probability_Progressive

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoDensityDyadicAverages.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Brownian
namespace Ito
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Pointwise truncation tendsto** (Brownian, mirror of Compensated). -/
 lemma truncation_pointwise_tendsto_brownian (x : ℝ) :
    Filter.Tendsto
      (fun M : ℕ => (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2)
      Filter.atTop (nhds 0) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventually_atTop.mpr ⟨⌈|x|⌉₊, fun M hM => ?_⟩
  have h_M_ge : (M : ℝ) ≥ |x| := by
    calc (M : ℝ) ≥ (⌈|x|⌉₊ : ℝ) := by exact_mod_cast hM
      _ ≥ |x| := Nat.le_ceil _
  have h_clip : max (-(M : ℝ)) (min (M : ℝ) x) = x := by
    have h_min : min (M : ℝ) x = x := min_eq_right (le_trans (le_abs_self _) h_M_ge)
    rw [h_min]
    exact max_eq_right (by linarith [neg_abs_le x])
  change (0 : ℝ≥0∞) = (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2
  rw [h_clip, sub_self]
  simp
/-- **Pointwise truncation dominated** (Brownian, mirror of Compensated). -/
 lemma truncation_dominated_brownian (x : ℝ) (M : ℕ) :
    (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2
      ≤ (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  have h_M_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h_abs : |x - max (-(M : ℝ)) (min (M : ℝ) x)| ≤ |x| := by
    by_cases hx : 0 ≤ x
    · by_cases hxM : x ≤ M
      · rw [min_eq_right hxM, max_eq_right (by linarith)]
        simp [abs_nonneg]
      · push Not at hxM
        rw [min_eq_left (le_of_lt hxM), max_eq_right (by linarith : -(M : ℝ) ≤ M)]
        rw [abs_of_nonneg (by linarith : 0 ≤ x - M), abs_of_nonneg hx]
        linarith
    · push Not at hx
      by_cases hxM : -(M : ℝ) ≤ x
      · rw [min_eq_right (by linarith : x ≤ M), max_eq_right hxM]
        simp
      · push Not at hxM
        rw [min_eq_right (by linarith : x ≤ M), max_eq_left (le_of_lt hxM)]
        rw [show x - -(M : ℝ) = x + M from by ring]
        rw [abs_of_nonpos (by linarith : x + (M : ℝ) ≤ 0), abs_of_neg hx]
        linarith
  have h_nn : ‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ ≤ ‖x‖₊ := by
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, Real.norm_eq_abs]
    exact h_abs
  exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr h_nn) 2
set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Truncation L² convergence (Brownian).** Mirror of Compensated. -/
lemma truncation_L2_converges_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ}
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Filter.Tendsto
      (fun M : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - max (-(M : ℝ)) (min (M : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) ?_ ?_ h_sq_int.ne ?_
  · -- AEMeasurable via Measurable.lintegral_prod_right'.
    intro M
    have h_F_joint : Measurable (fun (p : Ω × ℝ) =>
        (‖H p.1 p.2 - max (-(M : ℝ)) (min (M : ℝ) (H p.1 p.2))‖₊ : ℝ≥0∞) ^ 2) := by
      have h_clip : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
      have h_sub : Measurable (fun (p : Ω × ℝ) =>
          H p.1 p.2 - max (-(M : ℝ)) (min (M : ℝ) (H p.1 p.2))) :=
        h_meas.sub (h_clip.comp h_meas)
      exact (ENNReal.continuous_coe.measurable.comp h_sub.nnnorm).pow_const 2
    refine Measurable.aemeasurable ?_
    exact Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_F_joint
  · -- Bound: F_M ω ≤ G ω everywhere.
    intro M
    refine Filter.Eventually.of_forall (fun ω => ?_)
    refine MeasureTheory.lintegral_mono (fun s => ?_)
    exact LevyStochCalc.Brownian.Ito.truncation_dominated_brownian _ _
  · -- Pointwise: F_M ω → 0 for a.e. ω with finite inner integral.
    have h_finite_inner : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ := by
      have h_bound_h : Measurable (fun ω =>
          ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) :=
        Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0:ℝ) T))
          ((ENNReal.continuous_coe.measurable.comp h_meas.nnnorm).pow_const 2)
      exact MeasureTheory.ae_lt_top h_bound_h h_sq_int.ne
    filter_upwards [h_finite_inner] with ω h_ω_finite
    -- For this ω, apply DCT on the s-integral.
    rw [show (0 : ℝ≥0∞)
        = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0:ℝ) T)) from by simp]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2) ?_ ?_ h_ω_finite.ne ?_
    · intro M
      refine Measurable.aemeasurable ?_
      have h_clip : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
      have h_meas_slice : Measurable (fun s : ℝ => H ω s) :=
        h_meas.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s)))
      exact (ENNReal.continuous_coe.measurable.comp
        (h_meas_slice.sub (h_clip.comp h_meas_slice)).nnnorm).pow_const 2
    · intro M
      refine Filter.Eventually.of_forall (fun s => ?_)
      exact LevyStochCalc.Brownian.Ito.truncation_dominated_brownian _ _
    · refine Filter.Eventually.of_forall (fun s => ?_)
      exact LevyStochCalc.Brownian.Ito.truncation_pointwise_tendsto_brownian _
/-- Triangle inequality lifted to ENNReal:
`(‖x + y‖₊)² ≤ 2 · ((‖x‖₊)² + (‖y‖₊)²)`. Used to lift pointwise
bounds to lintegral bounds in the diagonal selection of
`simplePredictable_dense_L2`. -/
lemma sq_nnnorm_add_le_two_mul_brownian (x y : ℝ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  have h_norm_sq : ∀ z : ℝ, (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) :=
    fun z => by
    rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from ofReal_norm z |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖z‖ ^ 2 = z ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
  rw [h_norm_sq, h_norm_sq, h_norm_sq]
  have h_real : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have h_nn_x : 0 ≤ x ^ 2 := sq_nonneg _
  have h_nn_y : 0 ≤ y ^ 2 := sq_nonneg _
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat]]
  rw [← ENNReal.ofReal_add h_nn_x h_nn_y, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact ENNReal.ofReal_le_ofReal h_real
/-- **Dyadic partition** of `[0, T]` at refinement level `n`:
`partition i = i * T / 2^n` for `i = 0, ..., 2^n`. -/
noncomputable def dyadicPartition_brownian (T : ℝ) (n : ℕ) :
    Fin (2 ^ n + 1) → ℝ :=
  fun i => (i : ℝ) * T / (2 ^ n : ℕ)
lemma dyadicPartition_brownian_zero (T : ℝ) (n : ℕ) :
    dyadicPartition_brownian T n 0 = 0 := by
  simp [dyadicPartition_brownian]
lemma dyadicPartition_brownian_last (T : ℝ) (n : ℕ) :
    dyadicPartition_brownian T n (Fin.last (2 ^ n)) = T := by
  unfold dyadicPartition_brownian
  rw [Fin.val_last]
  field_simp
lemma dyadicPartition_brownian_strictMono {T : ℝ} (hT : 0 < T) (n : ℕ) :
    StrictMono (dyadicPartition_brownian T n) := by
  intro i j hij
  unfold dyadicPartition_brownian
  have h_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have h_lt : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  rw [div_lt_div_iff_of_pos_right h_pos]
  exact mul_lt_mul_of_pos_right h_lt hT
lemma dyadicPartition_brownian_le_T {T : ℝ} (_hT : 0 < T) (n : ℕ) :
    dyadicPartition_brownian T n (Fin.last (2 ^ n)) ≤ T :=
  le_of_eq (dyadicPartition_brownian_last T n)
/-- **Dyadic averaging coefficient**: the average of `g(ω, ·)` over the `i`-th
dyadic interval `(t_i, t_{i+1}]` of `[0, T]` at refinement level `n`.

Used as the ξ-coefficient of the dyadic SimplePredictable approximation. -/
noncomputable def dyadicAvg_brownian
    {T : ℝ} (g : Ω → ℝ → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) : ℝ :=
  ((2 ^ n : ℕ) / T) *
    ∫ s in Set.Ioc (dyadicPartition_brownian T n i.castSucc)
                    (dyadicPartition_brownian T n i.succ),
      g ω s
/-- Measurability of `dyadicAvg_brownian` in `ω` (Bochner integral commutes with
measurability via Fubini). -/
lemma dyadicAvg_brownian_measurable
    (T : ℝ) (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (n : ℕ) (i : Fin (2 ^ n)) :
    Measurable (dyadicAvg_brownian (T := T) g n i) := by
  unfold dyadicAvg_brownian
  refine Measurable.const_mul ?_ _
  -- The Bochner integral ∫ s in S, g ω s ∂volume = ∫ s, g ω s ∂(volume.restrict S)
  -- is measurable in ω by `StronglyMeasurable.integral_prod_right`.
  refine MeasureTheory.StronglyMeasurable.measurable ?_
  exact MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Set.Ioc (dyadicPartition_brownian T n i.castSucc)
                                    (dyadicPartition_brownian T n i.succ)))
    h_meas.stronglyMeasurable
/-- Length of dyadic interval at refinement level `n`: `T/2^n`. -/
lemma dyadicPartition_brownian_diff {T : ℝ} (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicPartition_brownian T n i.succ - dyadicPartition_brownian T n i.castSucc
      = T / (2 ^ n : ℕ) := by
  unfold dyadicPartition_brownian
  have hi_succ : ((i.succ : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) + 1 := by
    simp [Fin.val_succ]
  have hi_castSucc : ((i.castSucc : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) := by
    simp [Fin.val_castSucc]
  rw [hi_succ, hi_castSucc]
  ring
omit [MeasurableSpace Ω] in
/-- Boundedness of `dyadicAvg_brownian`: if `|g| ≤ M`, then `|dyadicAvg ω| ≤ M`. -/
lemma dyadicAvg_brownian_bounded
    (T : ℝ) (hT : 0 < T) (g : Ω → ℝ → ℝ)
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) :
    |dyadicAvg_brownian (T := T) g n i ω| ≤ M := by
  unfold dyadicAvg_brownian
  set t_i := dyadicPartition_brownian T n i.castSucc with ht_i
  set t_succ := dyadicPartition_brownian T n i.succ with ht_succ
  have h_lt : t_i < t_succ :=
    dyadicPartition_brownian_strictMono hT n Fin.castSucc_lt_succ
  have h_le : t_i ≤ t_succ := le_of_lt h_lt
  have h_diff : t_succ - t_i = T / (2 ^ n : ℕ) := by
    rw [ht_i, ht_succ]
    exact dyadicPartition_brownian_diff n i
  have h_M_nn : (0 : ℝ) ≤ M := le_trans (abs_nonneg (g ω 0)) (h_bound ω 0)
  have h_volume_eq : volume (Set.Ioc t_i t_succ) = ENNReal.ofReal (t_succ - t_i) :=
    Real.volume_Ioc
  -- ∫ s in (t_i, t_succ], g ω s = ∫ s, (Ioc t_i t_succ).indicator (g ω) s.
  -- ‖g ω s‖ ≤ M everywhere, so the indicator ‖g ω s‖ ≤ M·𝟙_{Ioc} a.e.
  have h_integral_norm_bound :
      ‖∫ s in Set.Ioc t_i t_succ, g ω s‖ ≤ M * (t_succ - t_i) := by
    have h_norm_le : ∀ᵐ s ∂(volume.restrict (Set.Ioc t_i t_succ)),
        ‖g ω s‖ ≤ M := by
      refine Filter.Eventually.of_forall (fun s => ?_)
      rw [Real.norm_eq_abs]
      exact h_bound ω s
    haveI h_finite_restrict :
        MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Ioc t_i t_succ)) := by
      refine ⟨?_⟩
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          h_volume_eq]
      exact ENNReal.ofReal_lt_top
    have h_M_integrable : MeasureTheory.Integrable
        (fun _ => M) (volume.restrict (Set.Ioc t_i t_succ)) :=
      MeasureTheory.integrable_const M
    calc ‖∫ s in Set.Ioc t_i t_succ, g ω s‖
        ≤ ∫ _ in Set.Ioc t_i t_succ, M ∂volume :=
          MeasureTheory.norm_integral_le_of_norm_le h_M_integrable h_norm_le
      _ = M * (t_succ - t_i) := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul]
          have h_real : volume.real (Set.Ioc t_i t_succ) = t_succ - t_i := by
            unfold MeasureTheory.Measure.real
            rw [h_volume_eq, ENNReal.toReal_ofReal (by linarith)]
          rw [h_real]
          ring
  rw [Real.norm_eq_abs] at h_integral_norm_bound
  -- Combine.
  have h_pow_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have h_coeff_pos : (0 : ℝ) < (2 ^ n : ℕ) / T := div_pos h_pow_pos hT
  rw [abs_mul, abs_of_pos h_coeff_pos]
  calc ((2 ^ n : ℕ) / T) * |∫ s in Set.Ioc t_i t_succ, g ω s|
      ≤ ((2 ^ n : ℕ) / T) * (M * (t_succ - t_i)) :=
        mul_le_mul_of_nonneg_left h_integral_norm_bound (le_of_lt h_coeff_pos)
    _ = ((2 ^ n : ℕ) / T) * (M * (T / (2 ^ n : ℕ))) := by rw [h_diff]
    _ = M := by
        have h_T_ne : T ≠ 0 := ne_of_gt hT
        have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pow_pos
        field_simp
end Ito
end Brownian
end LevyStochCalc


