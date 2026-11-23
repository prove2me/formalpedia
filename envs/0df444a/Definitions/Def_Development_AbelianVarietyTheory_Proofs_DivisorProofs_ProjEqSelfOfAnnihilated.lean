-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:54:31.683305+00:00
-- url     : https://prove2.me/theorems/a4d93a79-2610-4845-82a2-b69f6af13874
-- title:
--   Proj Eq Self Of Annihilated
-- statement:
--   Definitions and structural lemmas for Proj Eq Self Of Annihilated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProjEqSelfOfAnnihilated.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
namespace GlobalTheory.RealWeil.Vacuum
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}
def line (J : V ≃ₗᵢ[ℝ] V) (u : V) : ℂ →L[ℝ] V := reCLM.smulRight u + imCLM.smulRight (J u)
open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B} in
theorem _root_.GlobalTheory.RealWeil.Vacuum.line_apply (u : V) (ζ : ℂ) :
    _root_.GlobalTheory.RealWeil.Vacuum.line J u ζ = ζ.re • u + ζ.im • J u := by
  simp [_root_.GlobalTheory.RealWeil.Vacuum.line]
open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B} in
theorem inner_self_complexStructure_eq_zero (hJ : ∀ x, J (J x) = -x) (u : V) :
    ⟪u, J u⟫ = 0 := by
  have e := J.inner_map_map u (J u)
  rw [hJ, inner_neg_right, real_inner_comm u (J u)] at e
  linarith
open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B} in
theorem _root_.GlobalTheory.RealWeil.Vacuum.norm_line (hJ : ∀ x, J (J x) = -x) (u : V) (θ : ℝ) :
    ‖_root_.GlobalTheory.RealWeil.Vacuum.line J u (circleMap 0 1 θ)‖ = ‖u‖ := by
  have h0 := inner_self_complexStructure_eq_zero hJ u
  rw [_root_.GlobalTheory.RealWeil.Vacuum.line_apply, circleMap_zero, ofReal_one, one_mul,
    exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
    ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm u (J u), h0, LinearIsometryEquiv.inner_map_map, mul_zero, add_zero, zero_add]
  linear_combination ⟪u, u⟫ * Real.cos_sq_add_sin_sq θ
def rot [FiniteDimensional ℝ V] (hJ : ∀ x, J (J x) = -x) (θ : ℝ) : V ≃ₗᵢ[ℝ] V :=
  LinearIsometry.toLinearIsometryEquiv
    { toFun := fun u => line J u (circleMap 0 1 θ)
      map_add' := fun x y => by simp only [line_apply, map_add, smul_add]; abel
      map_smul' := fun a x => by simp only [line_apply, map_smul, smul_add, RingHom.id_apply, smul_comm a]
      norm_map' := fun u => norm_line hJ u θ } rfl
end GlobalTheory.RealWeil.Vacuum
namespace GlobalTheory.RealWeil
open Vacuum
end GlobalTheory.RealWeil
end


