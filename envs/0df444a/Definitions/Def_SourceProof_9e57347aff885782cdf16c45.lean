-- Prove2me | Definitions.Def_SourceProof_9e57347aff885782cdf16c45
-- name    : SourceProof_9e57347aff885782cdf16c45
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:25:43.254761+00:00
-- url     : https://prove2.me/theorems/150fe530-22ff-43b9-9970-8e7865ddad6d
-- title:
--   LevyStochCalc source module: SourceProof_9e57347aff885782cdf16c45
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.timeIndicator_sq_integral` comes from the `LevyStochCalc.Poisson.CompensatedDensityMarkSum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-sum process and its `L²` isometry

The process `∑ᵢ ∑ₖ ξᵢₖ Ñ((tᵢ, tᵢ₊₁] × Bₖ)` attached to adapted bounded coefficients, its second
moment as the `L²(P ⊗ ds ⊗ ν)` energy of the associated integrand, and the isometry for the
difference of two such processes. The energy is computed from the product form of the reference
intensity on time-mark boxes; completeness of `L²(P)` then turns a Cauchy sequence of such
processes into a limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_9e57347aff885782cdf16c45
    {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T) (f : Fin N₀ → ℝ) :
    ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * f i) ^ 2 ∂volume
      = ∑ i : Fin N₀, (p i.succ - p i.castSucc) * (f i) ^ 2 := by
  have hpnn : ∀ j : Fin (N₀ + 1), 0 ≤ p j := fun j => by
    have := hpmono.monotone (Fin.zero_le j); rwa [hp0] at this
  have hle : ∀ i : Fin N₀, p i.castSucc ≤ p i.succ := fun i => (hpmono Fin.castSucc_lt_succ).le
  have hsubT : ∀ i : Fin N₀, Set.Ioc (p i.castSucc) (p i.succ) ⊆ Set.Icc (0 : ℝ) T := by
    intro i x hx
    exact ⟨(hpnn _).trans hx.1.le, hx.2.trans ((hpmono.monotone (Fin.le_last _)).trans hpleT)⟩
  -- pointwise: the square collapses to the diagonal.
  have hpt : ∀ s, (∑ i : Fin N₀,
        (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s * f i) ^ 2
      = ∑ i : Fin N₀,
        (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s * (f i) ^ 2 := by
    intro s
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · by_cases hs : s ∈ Set.Ioc (p i.castSucc) (p i.succ) <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hs]; ring
    · intro i' _ hi'
      have hdisj : Disjoint (Set.Ioc (p i.castSucc) (p i.succ))
          (Set.Ioc (p i'.castSucc) (p i'.succ)) := by
        rw [Set.Ioc_disjoint_Ioc]
        rcases lt_or_gt_of_ne hi' with h | h
        · exact le_trans (min_le_right _ _)
            (le_trans (hpmono.monotone (Fin.succ_le_castSucc_iff.mpr h)) (le_max_left _ _))
        · exact le_trans (min_le_left _ _)
            (le_trans (hpmono.monotone (Fin.succ_le_castSucc_iff.mpr h)) (le_max_right _ _))
      by_cases hs : s ∈ Set.Ioc (p i.castSucc) (p i.succ)
      · have hns : s ∉ Set.Ioc (p i'.castSucc) (p i'.succ) := fun hs' => hdisj.le_bot ⟨hs, hs'⟩
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hs, hns]
      · simp [Set.indicator_of_notMem hs]
    · intro h; exact absurd (Finset.mem_univ i) h
  haveI hfin : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  have hintg : ∀ i : Fin N₀, MeasureTheory.Integrable
      (fun s => (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s * (f i) ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun i => ((MeasureTheory.integrable_const (1 : ℝ)).indicator measurableSet_Ioc).mul_const _
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s _ => hpt s),
    MeasureTheory.integral_finsetSum _ (fun i _ => hintg i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_mul_const, MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    MeasureTheory.setIntegral_const, Set.inter_eq_self_of_subset_right (hsubT i),
    Real.volume_real_Ioc_of_le (hle i), smul_eq_mul, mul_one]
end LevyStochCalc.Poisson.Compensated


