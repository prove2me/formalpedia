-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicUnitaryRes
-- name    : GroundTheory_AutomorphicForms_AnisotropicUnitaryRes
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:17:40.87897+00:00
-- url     : https://prove2.me/theorems/d34844aa-6f96-446f-8fab-ed58b22add89
-- title:
--   Anisotropic Unitary Res
-- statement:
--   Definitions and structural lemmas for Anisotropic Unitary Res, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_rmatHom_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
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
attribute [local simp] GroundTheory.Automorphic.Anisotropic.rmatHom_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Module Matrix TensorProduct
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
noncomputable section
namespace Anisotropic
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
local notation "𝒩" => Fintype.card (ι × κ)
def resHom : Matrix ι ι (R ⊗[K] E) →ₐ[R] Matrix (Fin 𝒩) (Fin 𝒩) R :=
  (Matrix.reindexAlgEquiv R R (Fintype.equivFin (ι × κ))).toAlgHom.comp (blockHom b R)
def resVec (x : ι → R ⊗[K] E) : Fin 𝒩 → R := coordsVec b R x ∘ (Fintype.equivFin (ι × κ)).symm
def ofResVec (y : Fin 𝒩 → R) : ι → R ⊗[K] E :=
  fun i => (coords b R).symm fun k => y (Fintype.equivFin (ι × κ) (i, k))
variable {R}
variable (R)
def trHom : GL ι (R ⊗[K] E) →* GL (Fin 𝒩) R where
  toFun g := ⟨resHom b R ((↑g⁻¹ : Matrix ι ι (R ⊗[K] E))ᵀ), resHom b R (((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E))ᵀ),
    by rw [← map_mul, ← transpose_mul, g.mul_inv, transpose_one, map_one],
    by rw [← map_mul, ← transpose_mul, g.inv_mul, transpose_one, map_one]⟩
  map_one' := by
    ext : 1
    simp
  map_mul' g h := by
    ext : 1
    simp [_root_.mul_inv_rev, transpose_mul, map_mul]
def resScalar (j : κ) : Matrix (Fin 𝒩) (Fin 𝒩) K :=
  resHom (ι := ι) b K (Matrix.scalar ι (baseBasis b K j))
variable {R}
variable (R)
def conjMat : Matrix κ κ R := fun k => coords b R (conjBase K E R (baseBasis b R k))
end Anisotropic
end
end GroundTheory.Automorphic


