-- Prove2me | Definitions.Def_SourceProof_59dc14df6f6315a597b2c358
-- name    : SourceProof_59dc14df6f6315a597b2c358
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:25:26.601159+00:00
-- url     : https://prove2.me/theorems/834bc44b-40a3-483b-863b-c9a6f2fb9d6b
-- title:
--   LevyStochCalc source module: SourceProof_59dc14df6f6315a597b2c358
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.dyadicAvg_brownian_bounded` comes from the `LevyStochCalc.Brownian.ItoDensityDyadicAverages` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncation in `L²` and dyadic cell averages

Truncation of an `L²(Ω × [0,T])` integrand at level `M` together with the `L²` error it
incurs, the dyadic partition of `[0,T]`, the cell averages of an integrand over the
partition intervals, and the simple predictable process whose values on the `n`-th dyadic
grid are those averages.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- `omit` the unused `[MeasurableSpace Ω]` section variable (this lemma's
-- `g : Ω → ℝ → ℝ` does not need it).
omit [MeasurableSpace Ω] in

theorem _root_.Prove2MeSourceProof.h_59dc14df6f6315a597b2c358
    (T : ℝ) (hT : 0 < T) (g : Ω → ℝ → ℝ)
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) :
    |dyadicAvg_brownian (T := T) g n i ω| ≤ M := by
  unfold LevyStochCalc.Brownian.Ito.dyadicAvg_brownian
  set t_i := LevyStochCalc.Brownian.Ito.dyadicPartition_brownian T n i.castSucc with ht_i
  set t_succ := LevyStochCalc.Brownian.Ito.dyadicPartition_brownian T n i.succ with ht_succ
  have h_lt : t_i < t_succ :=
    LevyStochCalc.Brownian.Ito.dyadicPartition_brownian_strictMono hT n Fin.castSucc_lt_succ
  have h_le : t_i ≤ t_succ := le_of_lt h_lt
  have h_diff : t_succ - t_i = T / (2 ^ n : ℕ) := by
    rw [ht_i, ht_succ]
    exact LevyStochCalc.Brownian.Ito.dyadicPartition_brownian_diff n i
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
end LevyStochCalc.Brownian.Ito


