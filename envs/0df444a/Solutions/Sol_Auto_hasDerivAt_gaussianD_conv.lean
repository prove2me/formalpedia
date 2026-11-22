-- Prove2me | solution 1 for Auto.hasDerivAt_gaussianD_conv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:03:29.578688+00:00
-- url     : https://prove2.me/submissions/e400d47d-9db1-411a-8ec9-ebc4b6e5fd21

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_abs_gaussianD_le_const

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal symmDiff
noncomputable section
open Real
namespace Auto
theorem _root_.solution (i : ℕ) {σ : ℝ} (hσ : 0 < σ) {G : ℝ → ℝ} (hG : Integrable G)
    (t : ℝ) :
    HasDerivAt (fun t => ∫ d, gaussianD i σ (t - d) * G d) (∫ d, gaussianD (i + 1) σ (t - d) * G
      d) t := by
  obtain ⟨M0, hM0⟩ := abs_gaussianD_le_const i hσ
  obtain ⟨M1, hM1⟩ := abs_gaussianD_le_const (i + 1) hσ
  have hint : ∀ (k : ℕ) (M : ℝ), (∀ t, |gaussianD k σ t| ≤ M) → ∀ x : ℝ,
      Integrable (fun d => gaussianD k σ (x - d) * G d) := by
    intro k M hM x
    refine (hG.norm.const_mul M).mono' ?_ ?_
    · exact ((continuous_gaussianD k σ).comp (continuous_const.sub continuous_id)
        ).aestronglyMeasurable.mul hG.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun d => ?_
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun d => M1 * |G d|) (F := fun
      t d => gaussianD i σ (t - d) * G d) (F' := fun t d => gaussianD (i + 1) σ (t - d) * G d) (s :=
      Set.univ)
    Filter.univ_mem ?_ (hint i M0 hM0 t) ?_ ?_ (hG.norm.const_mul M1) ?_).2
  · exact Filter.Eventually.of_forall fun x => (hint i M0 hM0 x).aestronglyMeasurable
  · exact (hint (i + 1) M1 hM1 t).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun d x _ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hM1 _) (abs_nonneg _)
  · refine Filter.Eventually.of_forall fun d x _ => ?_
    have := ((hasDerivAt_gaussianD i σ (x - d)).comp x ((hasDerivAt_id x).sub_const d)).mul_const (G
        d)
    simpa using this
end Auto
