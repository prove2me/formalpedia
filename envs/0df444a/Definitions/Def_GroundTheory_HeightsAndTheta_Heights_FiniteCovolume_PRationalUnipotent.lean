-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRationalUnipotent
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRationalUnipotent
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T04:19:50.123452+00:00
-- url     : https://prove2.me/theorems/c35cf6cf-5262-4aa8-b0c3-47e3f57ee006
-- title:
--   PRational Unipotent
-- statement:
--   Definitions and structural lemmas for PRational Unipotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRationalUnipotent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
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
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
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
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
namespace RationalUnipotent
def unipMap (h : HermitianForm F E W) (x₀ y : W) (c : E) : W →ₗ[E] W where
  toFun x := x + (h.toSesq x₀ x * c - h.toSesq y x) • x₀ + h.toSesq x₀ x • y
  map_add' a b := by
    simp only [map_add]
    module
  map_smul' r a := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    module
omit [NumberField E] in
theorem unipMap_apply (h : HermitianForm F E W) (x₀ y : W) (c : E) (x : W) :
    unipMap h x₀ y c x = x + (h.toSesq x₀ x * c - h.toSesq y x) • x₀ + h.toSesq x₀ x • y := rfl
omit [NumberField E] in

theorem sesq_swap (h : HermitianForm F E W) (u v : W) :
    h.toSesq u v = conj F E (h.toSesq v u) :=
  (h.isSymm.eq v u).symm
omit [NumberField E] in

theorem sesq_smul_left (h : HermitianForm F E W) (r : E) (u v : W) :
    h.toSesq (r • u) v = conj F E r * h.toSesq u v := by
  rw [LinearMap.map_smulₛₗ₂]
  rfl
theorem unipMap_unipMap (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    unipMap h x₀ y c (unipMap h x₀ (-y) (conj F E c) x) = x := by
  have hy' : h.toSesq y x₀ = 0 := by rw [sesq_swap, hy, map_zero]
  simp only [unipMap_apply, map_add, map_smul, map_neg, LinearMap.neg_apply, hx₀, hy, hy']
  have key : h.toSesq x₀ x * conj F E c - -h.toSesq y x +
      (h.toSesq x₀ x * c - (h.toSesq y x + -(h.toSesq x₀ x * h.toSesq y y))) = 0 := by
    linear_combination h.toSesq x₀ x * hc
  linear_combination (norm := module) key • x₀
theorem sesq_unipMap (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x x' : W) :
    h.toSesq (unipMap h x₀ y c x) (unipMap h x₀ y c x') = h.toSesq x x' := by
  have hy' : h.toSesq y x₀ = 0 := by rw [sesq_swap, hy, map_zero]
  simp only [unipMap_apply, map_add, map_smul, smul_eq_mul, LinearMap.add_apply,
    sesq_smul_left, hx₀, hy, hy', map_sub, map_mul, mul_zero, add_zero]
  rw [sesq_swap h x x₀, sesq_swap h x y]
  linear_combination conj F E (h.toSesq x₀ x) * h.toSesq x₀ x' * hc
def unipElem (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) : h.unitaryGroup :=
  ⟨LinearEquiv.ofLinearMap (unipMap h x₀ y c) (unipMap h x₀ (-y) (conj F E c))
    (LinearMap.ext fun x => unipMap_unipMap h hx₀ hy hc x)
    (LinearMap.ext fun x => by
      have e := unipMap_unipMap h (y := -y) (c := conj F E c) hx₀
        (by rw [map_neg, hy, neg_zero])
        (by rw [conj_conj, add_comm, hc, map_neg, LinearMap.map_neg₂, neg_neg]) x
      rwa [neg_neg, conj_conj] at e),
    fun x x' => sesq_unipMap h hx₀ hy hc x x'⟩
end RationalUnipotent
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


