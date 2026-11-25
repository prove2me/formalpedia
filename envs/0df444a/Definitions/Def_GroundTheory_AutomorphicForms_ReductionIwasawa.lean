-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
-- name    : GroundTheory_AutomorphicForms_ReductionIwasawa
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:41:01.275802+00:00
-- url     : https://prove2.me/theorems/cdc1cd7b-25d6-4e4f-9dbf-c4384c2997c3
-- title:
--   Reduction Iwasawa
-- statement:
--   Definitions and structural lemmas for Reduction Iwasawa, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_diagonal_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finAt_mul
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finEval_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_mul
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infEval_apply
import Theorems.Thm_GroundTheory_Automorphic_RestrictedProduct_matrixUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_coe_iwasawaHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.AdelicGLn.diagonal_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Reduction.finAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.finEval_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infEval_apply
attribute [local simp] GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
attribute [local simp] GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
namespace GroundTheory.Automorphic
noncomputable section
namespace Reduction
section Unitary
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
end Unitary
section Transport
variable {E 𝕜 : Type*} [NormedField E] [RCLike 𝕜] {n : ℕ}
end Transport
variable {K : Type*} [Field K] {n : ℕ}
def archCompact (w : InfinitePlace K) : Subgroup (GL (Fin n) w.Completion) where
  carrier := {k | ∀ y : Fin n → w.Completion,
    euclidNorm (y ᵥ* (k : Matrix (Fin n) (Fin n) w.Completion)) = euclidNorm y}
  one_mem' y := by simp
  mul_mem' {a b} ha hb y := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Units.val_mul, ← vecMul_vecMul, hb, ha]
  inv_mem' {k} hk y := by
    simp only [Set.mem_ofPred_eq] at hk ⊢
    have := hk (y ᵥ* ((k⁻¹ : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion))
    rw [vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one] at this
    exact this.symm
variable [NumberField K]
@[simp] theorem infAt_one (w : InfinitePlace K) : infAt w (1 : AdelicGLn.AdelicGL K n) = 1 := by
  simp [infAt]
@[simp] theorem finAt_one (v : HeightOneSpectrum (𝓞 K)) :
    finAt v (1 : AdelicGLn.AdelicGL K n) = 1 := by
  simp [finAt]
theorem infAt_inv (w : InfinitePlace K) (g : AdelicGLn.AdelicGL K n) :
    infAt w g⁻¹ = (infAt w g)⁻¹ := by
  simp [infAt, map_inv]
theorem finAt_inv (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGLn.AdelicGL K n) :
    finAt v g⁻¹ = (finAt v g)⁻¹ := by
  simp [finAt, map_inv, RestrictedProduct.inv_apply]
def maxCompact : Subgroup (AdelicGLn.AdelicGL K n) where
  carrier := {k | (∀ w, infAt w k ∈ archCompact w) ∧
    ∀ v, finAt v k ∈ GLnLocal.integralGL (v.adicCompletion K) n}
  one_mem' := ⟨fun w => by rw [infAt_one]; exact one_mem _,
    fun v => by rw [finAt_one]; exact one_mem _⟩
  mul_mem' {a b} ha hb := ⟨fun w => by rw [infAt_mul]; exact mul_mem (ha.1 w) (hb.1 w),
    fun v => by rw [finAt_mul]; exact mul_mem (ha.2 v) (hb.2 v)⟩
  inv_mem' {k} hk := ⟨fun w => by rw [infAt_inv]; exact inv_mem (hk.1 w),
    fun v => by rw [finAt_inv]; exact inv_mem (hk.2 v)⟩
def adelicBorel : Subgroup (AdelicGLn.AdelicGL K n) where
  carrier := {b | (b : Matrix (Fin n) (Fin n) 𝔸[K]).IsUpperTriangular}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at ha hb ⊢
    exact ha.mul hb
  inv_mem' {b} hb := by
    simp only [Set.mem_ofPred_eq] at hb ⊢
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
end Reduction
end
end GroundTheory.Automorphic


