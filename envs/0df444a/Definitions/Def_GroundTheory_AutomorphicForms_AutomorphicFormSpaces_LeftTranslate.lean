-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_AutomorphicFormSpaces_LeftTranslate
-- name    : GroundTheory_AutomorphicForms_AutomorphicFormSpaces_LeftTranslate
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:27:20.719021+00:00
-- url     : https://prove2.me/theorems/cc16da34-d955-4110-b62e-46c2855db57a
-- title:
--   Left Translate
-- statement:
--   Definitions and structural lemmas for Left Translate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AutomorphicFormSpaces/LeftTranslate.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a


set_option autoImplicit false
namespace GroundTheory.Automorphic
open Set Filter Topology
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
def leftTranslate {M : Type*} [Mul M] {F : Type*} (a : M) (f : M → F) (g : M) : F := f (a * g)
@[simp] theorem leftTranslate_apply {M : Type*} [Mul M] {F : Type*} (a : M) (f : M → F) (g : M) :
    leftTranslate a f g = f (a * g) := rfl
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem isSmoothFun_leftTranslate {f : G → F} (hf : h.IsSmoothFun f) (a : G) :
    h.IsSmoothFun (leftTranslate a f) := by
  rw [h.isSmoothFun_iff] at hf ⊢
  intro g
  simpa only [leftTranslate, mul_assoc] using hf (a * g)
def leftTranslateEnd (a : G) : Module.End ℂ (h.smoothFuns (F := F)) where
  toFun f := ⟨leftTranslate a f, h.isSmoothFun_leftTranslate f.2 a⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem coe_leftTranslateEnd (a : G) (f : h.smoothFuns (F := F)) :
    ((h.leftTranslateEnd a f : h.smoothFuns (F := F)) : G → F) = leftTranslate a f := rfl
theorem leftTranslateEnd_mul (a b : G) :
    h.leftTranslateEnd (F := F) a * h.leftTranslateEnd b = h.leftTranslateEnd (b * a) :=
  LinearMap.ext fun f => Subtype.ext (funext fun g => by simp [leftTranslate, mul_assoc])
theorem leftTranslateEnd_one : h.leftTranslateEnd (F := F) 1 = 1 :=
  LinearMap.ext fun f => Subtype.ext (funext fun g => by simp [leftTranslate])
theorem leftTranslateEnd_inv_mul (a : G) :
    h.leftTranslateEnd (F := F) a⁻¹ * h.leftTranslateEnd a = 1 := by
  rw [leftTranslateEnd_mul, mul_inv_cancel, leftTranslateEnd_one]
theorem leftTranslateEnd_mul_inv (a : G) :
    h.leftTranslateEnd (F := F) a * h.leftTranslateEnd a⁻¹ = 1 := by
  rw [leftTranslateEnd_mul, inv_mul_cancel, leftTranslateEnd_one]
def conjLeft (a : G) :
    Module.End ℂ (h.smoothFuns (F := F)) →ₐ[ℝ] Module.End ℂ (h.smoothFuns (F := F)) where
  toFun T := h.leftTranslateEnd a⁻¹ * T * h.leftTranslateEnd a
  map_one' := by rw [mul_one, leftTranslateEnd_inv_mul]
  map_mul' S T := by
    calc h.leftTranslateEnd a⁻¹ * (S * T) * h.leftTranslateEnd a
        = h.leftTranslateEnd a⁻¹ * S * (h.leftTranslateEnd a * h.leftTranslateEnd a⁻¹) * T *
            h.leftTranslateEnd a := by rw [leftTranslateEnd_mul_inv]; simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_zero' := by simp
  map_add' S T := by simp [mul_add, add_mul]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one]
    rw [leftTranslateEnd_inv_mul]
end IsExpLieAlgebra
end GroundTheory.Automorphic


