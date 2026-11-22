-- Prove2me | solution 1 for Auto.triangular_bilinear_dense_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:43:22.355529+00:00
-- url     : https://prove2.me/submissions/fc988a39-49a6-45a1-916e-a576dff9e93c

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {𝕜 E V W : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace
    W]
namespace Auto
theorem _root_.solution (e : E →ₗ[𝕜] V) (hd : DenseRange e)
    (B : E →ₗ[𝕜] E →ₗ[𝕜] W) {C : ℝ} (hC : 0 ≤ C) (hB : ∀ a b, ‖B a b‖ ≤ C * ‖e a‖ * ‖e b‖) :
    ∃ B' : V →L[𝕜] V →L[𝕜] W, (∀ a b, B' (e a) (e b) = B a b) ∧ ∀ x, ‖B' x‖ ≤ C * ‖x‖ := by
  have hb₂ : ∀ a b, ‖B a b‖ ≤ (C * ‖e a‖) * ‖e b‖ := hB
  let B₁ : E →ₗ[𝕜] (V →L[𝕜] W) :=
    { toFun := fun a => (B a).extendOfNorm e
      map_add' := fun a a' => by
        apply LinearMap.extendOfNorm_unique hd (C * ‖e (a + a')‖) (hb₂ (a + a'))
        ext b
        simp [LinearMap.extendOfNorm_eq hd ⟨_, hb₂ a⟩, LinearMap.extendOfNorm_eq hd ⟨_, hb₂ a'⟩]
      map_smul' := fun r a => by
        apply LinearMap.extendOfNorm_unique hd (C * ‖e (r • a)‖) (hb₂ (r • a))
        ext b
        simp [LinearMap.extendOfNorm_eq hd ⟨_, hb₂ a⟩] }
  have hB₁ : ∀ a b, B₁ a (e b) = B a b := fun a b => LinearMap.extendOfNorm_eq hd ⟨_, hb₂ a⟩ b
  have hb₁ : ∀ a, ‖B₁ a‖ ≤ C * ‖e a‖ := fun a =>
    LinearMap.opNorm_extendOfNorm_le hd (by positivity) (hb₂ a)
  refine ⟨B₁.extendOfNorm e, fun a b => ?_, LinearMap.norm_extendOfNorm_apply_le hd C hb₁⟩
  rw [LinearMap.extendOfNorm_eq hd ⟨_, hb₁⟩ a, hB₁]
end Auto
