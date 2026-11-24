-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesRing
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:26.472512+00:00
-- url     : https://prove2.me/theorems/65c444de-62ab-4566-aa1d-ea46177e2f68
-- title:
--   PInt Series Ring
-- statement:
--   Definitions and structural lemmas for PInt Series Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesRing.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries Finset
noncomputable section
namespace IntSeriesRing
theorem conv_add {F G : PowerSeries ℤ} {r : ℝ} (hr : 0 ≤ r) (hF : IntSeriesConv F r)
    (hG : IntSeriesConv G r) : IntSeriesConv (F + G) r :=
  Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr n))
    (fun n ↦ by
      rw [← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr n)
      simpa using abs_add_le ((coeff n F : ℤ) : ℝ) ((coeff n G : ℤ) : ℝ)) (hF.add hG)
theorem conv_neg {F : PowerSeries ℤ} {r : ℝ} (hF : IntSeriesConv F r) : IntSeriesConv (-F) r := by
  simpa [IntSeriesConv] using hF
theorem conv_one (r : ℝ) : IntSeriesConv 1 r := by
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [coeff_one, hn]
theorem conv_zero (r : ℝ) : IntSeriesConv 0 r := by
  simp [IntSeriesConv]
theorem conv_mul {F G : PowerSeries ℤ} {r : ℝ} (hr : 0 ≤ r) (hF : IntSeriesConv F r)
    (hG : IntSeriesConv G r) : IntSeriesConv (F * G) r := by
  have hf0 : ∀ n, 0 ≤ |((coeff n F : ℤ) : ℝ)| * r ^ n :=
    fun n ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr n)
  have hg0 : ∀ n, 0 ≤ |((coeff n G : ℤ) : ℝ)| * r ^ n :=
    fun n ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr n)
  have hS := summable_norm_sum_mul_antidiagonal_of_summable_norm
    (f := fun n ↦ |((coeff n F : ℤ) : ℝ)| * r ^ n) (g := fun n ↦ |((coeff n G : ℤ) : ℝ)| * r ^ n)
    ((show Summable _ from hF).congr fun n ↦ (Real.norm_of_nonneg (hf0 n)).symm)
    ((show Summable _ from hG).congr fun n ↦ (Real.norm_of_nonneg (hg0 n)).symm)
  refine Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr n))
    (fun n ↦ ?_) hS
  rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ mul_nonneg (hf0 _) (hg0 _)), coeff_mul]
  push_cast
  calc |∑ q ∈ antidiagonal n, ((coeff q.1 F : ℤ) : ℝ) * ((coeff q.2 G : ℤ) : ℝ)| * r ^ n
      ≤ (∑ q ∈ antidiagonal n, |((coeff q.1 F : ℤ) : ℝ) * ((coeff q.2 G : ℤ) : ℝ)|) * r ^ n :=
        mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (pow_nonneg hr n)
    _ = ∑ q ∈ antidiagonal n, |((coeff q.1 F : ℤ) : ℝ)| * r ^ q.1 *
          (|((coeff q.2 G : ℤ) : ℝ)| * r ^ q.2) := by
        rw [sum_mul]
        refine sum_congr rfl fun q hq ↦ ?_
        rw [HasAntidiagonal.mem_antidiagonal] at hq
        rw [abs_mul, ← hq, pow_add]
        ring
def convSubring (r : ℝ) (hr : 0 ≤ r) : Subring (PowerSeries ℤ) where
  carrier := {F | IntSeriesConv F r}
  mul_mem' := conv_mul hr
  one_mem' := conv_one r
  add_mem' := conv_add hr
  zero_mem' := conv_zero r
  neg_mem' := conv_neg
end IntSeriesRing
end
end GroundTheory.Heights₂.Heights.ChowlaSelberg


