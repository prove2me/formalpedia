-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorFderivFormula
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorFderivFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:40:15.900929+00:00
-- url     : https://prove2.me/theorems/85a34818-8dc4-4cc4-bc54-31b2c7ecaa84
-- title:
--   Partial Operator Fderiv Formula
-- statement:
--   Definitions and structural lemmas for Partial Operator Fderiv Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PartialOperatorFderivFormula.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SeminormSliceRLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivPdLe
import Theorems.Thm_GlobalTheory_SliceOp_pd_apply
import Theorems.Thm_GlobalTheory_SliceSchwartz_sliceRL_apply
import Theorems.Thm_GlobalTheory_SliceSchwartz_sliceR_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SliceSchwartz.sliceR_apply


set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
namespace GlobalTheory.SliceOpDeriv
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
theorem pd_padL_add (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (h h' : κ → V) :
    pd (padL (κ' := κ') (h + h')) f = pd (padL h) f + pd (padL h') f := by
  have e : (padL (κ' := κ') (h + h') : κ ⊕ κ' → V) = padL h + padL h' := by
    funext i; cases i <;> simp [padL]
  ext z
  rw [SchwartzMap.add_apply, pd_apply, pd_apply, pd_apply, e, map_add]
theorem pd_padL_smul (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (c : ℝ) (h : κ → V) :
    pd (padL (κ' := κ') (c • h)) f = (c : ℂ) • pd (padL h) f := by
  have e : (padL (κ' := κ') (c • h) : κ ⊕ κ' → V) = c • padL h := by
    funext i; cases i <;> simp [padL]
  ext z
  rw [SchwartzMap.smul_apply, pd_apply, pd_apply, e, map_smul, Complex.real_smul, smul_eq_mul]
def xPartL (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) : (κ → V) →ₗ[ℝ] ℂ where
  toFun h := P (sliceR (pd (padL (κ' := κ') h) f) x) y
  map_add' h h' := by
    simp only [pd_padL_add, ← sliceRL_apply, map_add, SchwartzMap.add_apply]
  map_smul' c h := by
    simp only [pd_padL_smul, ← sliceRL_apply, map_smul, SchwartzMap.smul_apply, RingHom.id_apply,
      Complex.real_smul, smul_eq_mul]
variable [FiniteDimensional ℝ V]
def xPart (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x : κ → V) (y : κ₁' → V) : (κ → V) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (xPartL P f x y)
end GlobalTheory.SliceOpDeriv
namespace GlobalTheory.SliceOpDeriv
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
end GlobalTheory.SliceOpDeriv
namespace GlobalTheory.SliceOpDeriv
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
def splitL : (κ ⊕ κ₁' → V) →L[ℝ] (κ → V) × (κ₁' → V) :=
  (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ ⊕ κ₁' => V) (Sum.inl i)).prod
    (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ ⊕ κ₁' => V) (Sum.inr j))
end GlobalTheory.SliceOpDeriv


