-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
-- name    : GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T07:48:18.004562+00:00
-- url     : https://prove2.me/theorems/875cfcad-604a-5db4-bf94-cc410dbe237e
-- title:
--   Hecke Char Ray Class
-- statement:
--   Definitions and structural lemmas for Hecke Char Ray Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup_iff_toFinite_mem
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
import Theorems.Thm_GroundTheory_Global_existsUnique_complexUnits_circle
import Theorems.Thm_GroundTheory_Global_existsUnique_realUnits_circle
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.HeckeCharacter.toIdele_diagonal
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.coe_circleToUnits
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing
namespace GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
section Completions
open NumberField.InfinitePlace.Completion
def realUnitsHom {w : InfinitePlace K} (hw : w.IsReal) : ℝˣ →ₜ* (w.Completion)ˣ where
  toMonoidHom := Units.map ((ringEquivRealOfIsReal hw).symm : ℝ →+* w.Completion).toMonoidHom
  continuous_toFun := Units.continuous_map (isometryEquivRealOfIsReal hw).symm.continuous
def complexUnitsHom {w : InfinitePlace K} (hw : w.IsComplex) : ℂˣ →ₜ* (w.Completion)ˣ where
  toMonoidHom := Units.map ((ringEquivComplexOfIsComplex hw).symm : ℂ →+* w.Completion).toMonoidHom
  continuous_toFun := Units.continuous_map (isometryEquivComplexOfIsComplex hw).symm.continuous
end Completions
namespace IdeleGroup
def ofInfinite : (InfiniteAdeleRing K)ˣ →* IdeleGroup K :=
  (ContinuousMulEquiv.symm (prodEquiv K)).toMulEquiv.toMonoidHom.comp (MonoidHom.inl _ _)
@[simp]
theorem toInfinite_ofInfinite (x : (InfiniteAdeleRing K)ˣ) : toInfinite K (ofInfinite x) = x := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (x, 1))).1 = x
  rw [ContinuousMulEquiv.apply_symm_apply]
@[simp]
theorem toFinite_ofInfinite (x : (InfiniteAdeleRing K)ˣ) : toFinite K (ofInfinite x) = 1 := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (x, 1))).2 = 1
  rw [ContinuousMulEquiv.apply_symm_apply]
def infiniteComponent (w : InfinitePlace K) : (InfiniteAdeleRing K)ˣ →* (w.Completion)ˣ :=
  Units.map (Pi.evalMonoidHom (fun u : InfinitePlace K ↦ u.Completion) w)
omit [NumberField K] in
@[simp]
theorem coe_infiniteComponent (w : InfinitePlace K) (x : (InfiniteAdeleRing K)ˣ) :
    ((infiniteComponent w x : (w.Completion)ˣ) : w.Completion) = (x : InfiniteAdeleRing K) w :=
  rfl
variable (K) in

def infinitePositive : Subgroup (InfiniteAdeleRing K)ˣ where
  carrier := {x | ∀ (w : InfinitePlace K) (hw : w.IsReal),
    0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((x : InfiniteAdeleRing K) w)}
  one_mem' w hw := by
    show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (1 : w.Completion)
    rw [map_one]
    exact one_pos
  mul_mem' {a b} ha hb w hw := by
    show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
      ((a : InfiniteAdeleRing K) w * (b : InfiniteAdeleRing K) w)
    rw [map_mul]
    exact mul_pos (ha w hw) (hb w hw)
  inv_mem' {a} ha w hw := by
    have h0 : ((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w *
        (a : InfiniteAdeleRing K) w = 1 :=
      congrFun a.inv_mul w
    have h1 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        (((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w) *
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((a : InfiniteAdeleRing K) w) = 1 := by
      rw [← map_mul, h0, map_one]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_pos.2 (ha w hw)
omit [NumberField K] in
theorem mem_infinitePositive {x : (InfiniteAdeleRing K)ˣ} :
    x ∈ infinitePositive K ↔ ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((x : InfiniteAdeleRing K) w) :=
  Iff.rfl
variable (K) in

def infiniteSign : (InfiniteAdeleRing K)ˣ →* ({w : InfinitePlace K // w.IsReal} → SignTypeˣ) :=
  MonoidHom.pi fun w ↦ (Units.map (signHom : ℝ →*₀ SignType).toMonoidHom).comp
    ((Units.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 :
      w.1.Completion →+* ℝ).toMonoidHom).comp (infiniteComponent w.1))
omit [NumberField K] in
theorem infiniteSign_apply_val (x : (InfiniteAdeleRing K)ˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    ((infiniteSign K x w : SignTypeˣ) : SignType) =
      SignType.sign (InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        ((x : InfiniteAdeleRing K) w.1)) :=
  rfl
omit [NumberField K] in

theorem infinitePositive_eq_ker : infinitePositive K = (infiniteSign K).ker := by
  ext x
  rw [mem_infinitePositive, MonoidHom.mem_ker]
  constructor
  · intro h
    funext w
    apply Units.ext
    rw [infiniteSign_apply_val, Pi.one_apply, Units.val_one, sign_eq_one_iff]
    exact h w.1 w.2
  · intro h w hw
    have h' := congrArg Units.val (congrFun h ⟨w, hw⟩)
    rwa [infiniteSign_apply_val, Pi.one_apply, Units.val_one, sign_eq_one_iff] at h'
instance : (infinitePositive K).FiniteIndex := by
  rw [infinitePositive_eq_ker]
  exact Subgroup.finiteIndex_ker _
variable (K) in

def rayGroup (𝔪 : Ideal (𝓞 K)) : Subgroup (IdeleGroup K) :=
  (diagonal K).range ⊔ (idealLevel 𝔪).map ofFinite ⊔ (infinitePositive K).map ofInfinite
def standardOpenInfiniteHom : standardOpenSubgroup K →* (InfiniteAdeleRing K)ˣ ⧸ infinitePositive K :=
  (QuotientGroup.mk' _).comp ((toInfinite K).comp (standardOpenSubgroup K).subtype)
def standardOpenFiniteHom (𝔪 : Ideal (𝓞 K)) :
    standardOpenSubgroup K →* finiteLevel (K := K) 0 ⧸ (idealLevel 𝔪).subgroupOf (finiteLevel 0) :=
  (QuotientGroup.mk' _).comp (((toFinite K).comp (standardOpenSubgroup K).subtype).codRestrict _
    fun u ↦ (mem_standardOpenSubgroup_iff_toFinite_mem _).1 u.2)
end IdeleGroup
open IdeleGroup
variable (K) in

abbrev RayClassGroup (𝔪 : Ideal (𝓞 K)) : Type _ := IdeleGroup K ⧸ rayGroup K 𝔪
namespace HeckeCharacter
variable (χ : HeckeCharacter K)
def realComponent {w : InfinitePlace K} (hw : w.IsReal) : ℝˣ →ₜ* Circle :=
  (χ.infiniteComponent w).comp (realUnitsHom hw)
def complexComponent {w : InfinitePlace K} (hw : w.IsComplex) : ℂˣ →ₜ* Circle :=
  (χ.infiniteComponent w).comp (complexUnitsHom hw)
def realParam {w : InfinitePlace K} (hw : w.IsReal) : Fin 2 × ℝ :=
  (existsUnique_realUnits_circle (χ.realComponent hw)).exists.choose
def complexParam {w : InfinitePlace K} (hw : w.IsComplex) : ℤ × ℝ :=
  (existsUnique_complexUnits_circle (χ.complexComponent hw)).exists.choose
end HeckeCharacter
end
end GroundTheory.Global


