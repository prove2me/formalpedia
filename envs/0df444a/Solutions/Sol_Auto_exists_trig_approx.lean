-- Prove2me | solution 1 for Auto.exists_trig_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:56:48.363165+00:00
-- url     : https://prove2.me/submissions/1c794eb9-4a59-4113-b471-839dd03cc262

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_fourier_mem_trigSubmodule
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution {f : ℝ → ℂ} (hf : Continuous f) (hp : Function.Periodic f 1) {δ : ℝ}
    (hδ : 0 < δ) : ∃ P : ℝ → ℂ, Continuous P ∧ Function.Periodic P 1 ∧
      (∃ K : ℕ, ∀ N ≥ K, ∀ x, fourierPartialSum P N x = P x) ∧ ∀ x, ‖f x - P x‖ < δ := by
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨hp.lift, continuous_coinduced_dom.mpr hf⟩
  have hF : F ∈ (Submodule.span ℂ (range fourier)).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hF
  obtain ⟨Q, hQ, hd⟩ := hF δ hδ
  have hQ' : Q ∈ trigSubmodule :=
    Submodule.span_le.mpr (range_subset_iff.mpr fourier_mem_trigSubmodule) hQ
  refine ⟨fun t => Q t, Q.continuous.comp continuous_quotient_mk', fun t => ?_, hQ', fun x => ?_⟩
  · simp only [AddCircle.coe_add_period]
  · rw [← dist_eq_norm]
    exact (ContinuousMap.dist_apply_le_dist (f := F) (g := Q) (x : AddCircle (1 : ℝ))).trans_lt hd
end Auto
