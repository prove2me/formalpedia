-- Prove2me | Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
-- name    : ClassicalComplexWPT_NormalizedCoefficients
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:00:36.292205+00:00
-- url     : https://prove2.me/theorems/ea477c43-66a0-5661-9e0d-4f3754336b6f
-- title:
--   Normalized Coefficients
-- statement:
--   Definitions and structural lemmas for Normalized Coefficients, from BochaoKong (BochaoKong/classical-complex-wpt; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Classical complex-analytic Weierstrass preparation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_lastTaylorCoefficient_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply


set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
namespace ClassicalComplexWPT
abbrev OriginSeq := L1Coeff ℕ
lemma norm_lastDirection_local (n : ℕ) : ‖lastDirection n‖ = 1 := by
  simp [lastDirection]
noncomputable def monomialSeq (d : ℕ) : OriginSeq := lp.single 1 d 1
@[simp] lemma monomialSeq_apply_same (d : ℕ) : monomialSeq d d = 1 := by
  simp [monomialSeq, lp.single_apply]
@[simp] lemma monomialSeq_apply_ne {d k : ℕ} (h : k ≠ d) : monomialSeq d k = 0 := by
  simp [monomialSeq, lp.single_apply, h]
noncomputable def scaleSeq (t : ℝ≥0) (ht : t ≤ 1) (f : OriginSeq) : OriginSeq :=
  ⟨fun k ↦ (t : ℂ) ^ k * f k, by
    apply memℓp_gen
    have hs : Summable (fun k ↦ ‖(t : ℂ) ^ k * f k‖) :=
      (L1Coeff.summable_norm f).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg t.coe_nonneg]
        simpa using mul_le_of_le_one_left (norm_nonneg (f k))
          (pow_le_one₀ t.coe_nonneg (by exact_mod_cast ht)))
    simpa using hs⟩
@[simp] lemma scaleSeq_apply (t : ℝ≥0) (ht : t ≤ 1) (f : OriginSeq) (k : ℕ) :
    scaleSeq t ht f k = (t : ℂ) ^ k * f k := rfl
noncomputable def normalizedScale (t : ℝ≥0) (ht : t ≤ 1)
    (f : OriginSeq) (d : ℕ) : OriginSeq :=
  ((scaleSeq t ht f d)⁻¹) • scaleSeq t ht f
@[simp] lemma normalizedScale_apply (t : ℝ≥0) (ht : t ≤ 1)
    (f : OriginSeq) (d k : ℕ) :
    normalizedScale t ht f d k =
      (((t : ℂ) ^ d * f d)⁻¹) * ((t : ℂ) ^ k * f k) := rfl
noncomputable def originWeightedCoeffs {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (R : ℝ≥0)
    (hR : (R : ℝ≥0∞) < p.radius) : OriginSeq :=
  ⟨fun k ↦ (R : ℂ) ^ k * lastTaylorCoefficient p k 0, by
    apply memℓp_gen
    have hs : Summable (fun k ↦ ‖(R : ℂ) ^ k * lastTaylorCoefficient p k 0‖) :=
      (p.summable_norm_mul_pow hR).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ by
        rw [lastTaylorCoefficient_zero, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg R.coe_nonneg]
        have hc : ‖p k (fun _ ↦ lastDirection n)‖ ≤ ‖p k‖ := by
          simpa [norm_lastDirection_local] using (p k).le_opNorm (fun _ ↦ lastDirection n)
        calc
          (R : ℝ) ^ k * ‖p k (fun _ ↦ lastDirection n)‖ ≤
              (R : ℝ) ^ k * ‖p k‖ :=
            mul_le_mul_of_nonneg_left hc (pow_nonneg R.coe_nonneg k)
          _ = ‖p k‖ * (R : ℝ) ^ k := mul_comm _ _)
    simpa using hs⟩
lemma mul_radius_lt_of_le_one {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (R t : ℝ≥0)
    (hR : (R : ℝ≥0∞) < p.radius) (ht : t ≤ 1) :
    ((t * R : ℝ≥0) : ℝ≥0∞) < p.radius := by
  apply lt_of_le_of_lt _ hR
  exact_mod_cast mul_le_of_le_one_left (show 0 ≤ R from bot_le) ht
noncomputable def normalizedOriginCoeffs {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : OriginSeq :=
  ((originWeightedCoeffs p r hr d)⁻¹) • originWeightedCoeffs p r hr
noncomputable def normalizedCoefficientMap {n : ℕ}
    (C : Base n → OriginSeq) (denom : ℂ) : Base n → OriginSeq :=
  fun z ↦ denom⁻¹ • C z
noncomputable def analyticNormalizedCoefficientMap {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : Base n → OriginSeq :=
  normalizedCoefficientMap (weightedCoefficientSeries p r).sum
    (originWeightedCoeffs p r hr d)
end ClassicalComplexWPT


