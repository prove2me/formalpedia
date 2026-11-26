-- Prove2me | Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
-- name    : ClassicalComplexWPT_WeightedCoefficientMap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T17:58:34.40258+00:00
-- url     : https://prove2.me/theorems/fd3e95bb-0410-4182-97fb-959d7f686372
-- title:
--   Weighted Coefficient Map
-- statement:
--   Definitions and structural lemmas for Weighted Coefficient Map, from BochaoKong (BochaoKong/classical-complex-wpt; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Classical complex-analytic Weierstrass preparation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero


set_option autoImplicit true
open scoped NNReal ENNReal Topology
namespace ClassicalComplexWPT
set_option maxHeartbeats 800000
noncomputable abbrev WeightedSeq := lp (fun _ : ℕ ↦ ℂ) 1
noncomputable def baseInclusion (n : ℕ) : Base n →L[ℂ] Ambient n :=
  ContinuousLinearMap.inl ℂ (Base n) ℂ
noncomputable def evalLast (n k : ℕ) :
    ((Ambient n)[×k]→L[ℂ] ℂ) →L[ℂ] ℂ :=
  ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ Ambient n) ℂ
    (fun _ ↦ lastDirection n)
@[simp] theorem norm_lastDirection (n : ℕ) : ‖lastDirection n‖ = 1 := by
  simp [lastDirection]
@[simp] theorem baseInclusion_apply (n : ℕ) (z : Base n) :
    baseInclusion n z = (z, 0) := rfl
noncomputable def lastCoefficientSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (k : ℕ) :
    FormalMultilinearSeries ℂ (Base n) ℂ :=
  (evalLast n k).compFormalMultilinearSeries
    ((p.changeOriginSeries k).compContinuousLinearMap (baseInclusion n))
noncomputable def weightedSingleCLM (r : ℝ≥0) (k : ℕ) :
    ℂ →L[ℂ] WeightedSeq :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ ↦ ℂ) 1 k).comp
    ((r : ℂ) ^ k • ContinuousLinearMap.id ℂ ℂ)
@[simp] theorem weightedSingleCLM_apply (r : ℝ≥0) (k : ℕ) (z : ℂ) :
    weightedSingleCLM r k z = lp.single 1 k ((r : ℂ) ^ k * z) := by
  rfl
noncomputable def weightedCoordinateSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (k : ℕ) :
    FormalMultilinearSeries ℂ (Base n) WeightedSeq :=
  (weightedSingleCLM r k).compFormalMultilinearSeries (lastCoefficientSeries p k)
noncomputable def weightedCoefficientSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) :
    FormalMultilinearSeries ℂ (Base n) WeightedSeq :=
  fun l ↦ ∑' k : ℕ, weightedCoordinateSeries p r k l
@[simp] theorem weightedCoordinateSeries_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (k l : ℕ)
    (v : Fin l → Base n) :
    weightedCoordinateSeries p r k l v =
      lp.single 1 k ((r : ℂ) ^ k *
        (p.changeOriginSeries k l) (fun i ↦ baseInclusion n (v i))
          (fun _ ↦ lastDirection n)) := by
  rfl
noncomputable def weightedLastCoeffs {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (x : Ambient n)
    (hr : (r : ℝ≥0∞) < (p.changeOrigin x).radius) : WeightedSeq :=
  ⟨fun k ↦ (r : ℂ) ^ k * p.changeOrigin x k (fun _ ↦ lastDirection n), by
    apply memℓp_gen
    have hs : Summable (fun k : ℕ ↦ ‖p.changeOrigin x k‖ * (r : ℝ) ^ k) :=
      (p.changeOrigin x).summable_norm_mul_pow hr
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ by
        show ‖(r : ℂ) ^ k * ((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
          ‖(p.changeOrigin x) k‖ * (r : ℝ) ^ k
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg r.coe_nonneg]
        have hv : ‖((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
            ‖(p.changeOrigin x) k‖ := by
          simpa [norm_lastDirection] using
            ((p.changeOrigin x) k).le_opNorm (fun _ ↦ lastDirection n)
        calc
          (r : ℝ) ^ k * ‖((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
              (r : ℝ) ^ k * ‖(p.changeOrigin x) k‖ :=
            mul_le_mul_of_nonneg_left hv (pow_nonneg r.coe_nonneg k)
          _ = ‖(p.changeOrigin x) k‖ * (r : ℝ) ^ k := mul_comm _ _)⟩
end ClassicalComplexWPT


