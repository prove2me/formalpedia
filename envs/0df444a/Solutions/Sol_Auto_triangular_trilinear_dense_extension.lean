-- Prove2me | solution 1 for Auto.triangular_trilinear_dense_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:45:01.857455+00:00
-- url     : https://prove2.me/submissions/8b9b0ee4-f832-4402-8bf5-0fb2c2b3e894

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
public import Theorems.Thm_Auto_triangular_bilinear_dense_extension
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
    (T : E →ₗ[𝕜] E →ₗ[𝕜] E →ₗ[𝕜] W) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ a b c, ‖T a b c‖ ≤ C * ‖e a‖ * ‖e b‖ * ‖e c‖) :
    ∃ T' : V →L[𝕜] V →L[𝕜] V →L[𝕜] W, (∀ a b c, T' (e a) (e b) (e c) = T a b c) ∧ (∀ x y z, ‖T'
      x y z‖ ≤ C * ‖x‖ * ‖y‖ * ‖z‖) ∧ ∀ S : V →L[𝕜] V →L[𝕜] V →L[𝕜] W, (∀ a b c, S (e a) (e b) (e
      c) = T a b c) → S = T' := by
  have hb₃ : ∀ a b c, ‖T a b c‖ ≤ (C * ‖e a‖ * ‖e b‖) * ‖e c‖ := hT
  have hT₁e : ∀ a b c, (T a b).extendOfNorm e (e c) = T a b c := fun a b c =>
    LinearMap.extendOfNorm_eq hd ⟨_, hb₃ a b⟩ c
  let T₁ : E →ₗ[𝕜] E →ₗ[𝕜] (V →L[𝕜] W) := LinearMap.mk₂ 𝕜
    (fun a b => (T a b).extendOfNorm e)
    (fun a a' b => by
      apply LinearMap.extendOfNorm_unique hd (C * ‖e (a + a')‖ * ‖e b‖) (hb₃ (a + a') b)
      ext c; simp [hT₁e])
    (fun r a b => by
      apply LinearMap.extendOfNorm_unique hd (C * ‖e (r • a)‖ * ‖e b‖) (hb₃ (r • a) b)
      ext c; simp [hT₁e])
    (fun a b b' => by
      apply LinearMap.extendOfNorm_unique hd (C * ‖e a‖ * ‖e (b + b')‖) (hb₃ a (b + b'))
      ext c; simp [hT₁e])
    (fun r a b => by
      apply LinearMap.extendOfNorm_unique hd (C * ‖e a‖ * ‖e (r • b)‖) (hb₃ a (r • b))
      ext c; simp [hT₁e])
  have hT₁ : ∀ a b c, T₁ a b (e c) = T a b c := hT₁e
  have hb₂ : ∀ a b, ‖T₁ a b‖ ≤ C * ‖e a‖ * ‖e b‖ := fun a b =>
    LinearMap.opNorm_extendOfNorm_le hd (by positivity) (hb₃ a b)
  obtain ⟨T', hT', hT'n⟩ := triangular_bilinear_dense_extension e hd T₁ hC hb₂
  refine ⟨T', fun a b c => by rw [hT', hT₁], fun x y z => ?_, fun S hS => ?_⟩
  · calc ‖T' x y z‖ ≤ ‖T' x y‖ * ‖z‖ := (T' x y).le_opNorm z
      _ ≤ ‖T' x‖ * ‖y‖ * ‖z‖ := by gcongr; exact (T' x).le_opNorm y
      _ ≤ C * ‖x‖ * ‖y‖ * ‖z‖ := by gcongr; exact hT'n x
  · have h₃ : ∀ a b, S (e a) (e b) = T' (e a) (e b) := fun a b =>
      ContinuousLinearMap.ext fun z => congrFun (hd.equalizer (S (e a) (e b)).continuous
        (T' (e a) (e b)).continuous (funext fun c => by simp [hS, hT', hT₁])) z
    have h₂ : ∀ a, S (e a) = T' (e a) := fun a =>
      ContinuousLinearMap.ext fun y => congrFun (hd.equalizer (S (e a)).continuous
        (T' (e a)).continuous (funext fun b => h₃ a b)) y
    exact ContinuousLinearMap.ext fun x => congrFun (hd.equalizer S.continuous T'.continuous
      (funext fun a => h₂ a)) x
end Auto
