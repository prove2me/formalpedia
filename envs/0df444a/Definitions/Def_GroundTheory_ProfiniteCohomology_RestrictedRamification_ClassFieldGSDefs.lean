-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ClassFieldGSDefs
-- name    : GroundTheory_ProfiniteCohomology_RestrictedRamification_ClassFieldGSDefs
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:25.100123+00:00
-- url     : https://prove2.me/theorems/9ec1ae92-9ea3-454b-b657-fc13bc93d915
-- title:
--   Class Field GSDefs
-- statement:
--   Definitions and structural lemmas for Class Field GSDefs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicDefs
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
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
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
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
def unitsOutside : Subgroup (IdeleGroup K) :=
  (⨅ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∈ S), (finiteProj v).ker) ⊓
    ⨅ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ S), (unitsLevel v 0).comap (finiteProj v)
def unitsOutsidePos : Subgroup (IdeleGroup K) :=
  unitsOutside S ⊓ positiveAt Set.univ
theorem unitsOutsidePos_le : unitsOutsidePos S ≤ unitsOutside S := inf_le_left
def sIdeleSubgroup : Subgroup (IdeleGroup K) :=
  (diagonal K).range ⊔ unitsOutside S
def sIdeleSubgroupPos : Subgroup (IdeleGroup K) :=
  (diagonal K).range ⊔ unitsOutsidePos S
theorem sIdeleSubgroupPos_le : sIdeleSubgroupPos S ≤ sIdeleSubgroup S :=
  sup_le_sup_left (unitsOutsidePos_le S) _
abbrev SIdeleClassGroup : Type _ := IdeleGroup K ⧸ sIdeleSubgroup S
abbrev SIdeleClassGroupPos : Type _ := IdeleGroup K ⧸ sIdeleSubgroupPos S
namespace SIdeleClassGroup
def mk : IdeleGroup K →* SIdeleClassGroup S := QuotientGroup.mk' _
theorem diagonal_range_le : (diagonal K).range ≤ sIdeleSubgroup S := le_sup_left
def ofIdeleClass : IdeleClassGroup K →* SIdeleClassGroup S :=
  QuotientGroup.map _ _ (MonoidHom.id _) (diagonal_range_le S)
end SIdeleClassGroup
namespace SIdeleClassGroupPos
def mk : IdeleGroup K →* SIdeleClassGroupPos S := QuotientGroup.mk' _
def toSIdeleClassGroup : SIdeleClassGroupPos S →* SIdeleClassGroup S :=
  QuotientGroup.map _ _ (MonoidHom.id _) (sIdeleSubgroupPos_le S)
end SIdeleClassGroupPos
def localUniformizer (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
  Units.mk0 (((v.valuation_exists_uniformizer K).choose : K) : v.adicCompletion K) (by
    intro h
    have h' := congrArg Valued.v h
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      (v.valuation_exists_uniformizer K).choose_spec, map_zero] at h'
    exact WithZero.exp_ne_zero h')
def divisorIdele : sDivisor S →+ Additive (IdeleGroup K) :=
  Finsupp.liftAddHom fun v ↦
    zmultiplesHom _ (Additive.ofMul (finiteEmbedding v.1 (localUniformizer v.1)))
def placesIdele [Finite S] : (∀ w : S, (w.1.adicCompletion K)ˣ) →* IdeleGroup K :=
  letI := Fintype.ofFinite S
  { toFun := fun a ↦ ∏ w : S, finiteEmbedding w.1 (a w)
    map_one' := by simp
    map_mul' := fun a b ↦ by
      simp only [Pi.mul_apply, map_mul]
      exact Finset.prod_mul_distrib }
def sPresentation [Finite S] :
    (∀ w : S, (w.1.adicCompletion K)ˣ) × Multiplicative (sDivisor S) →* SIdeleClassGroup S :=
  (SIdeleClassGroup.mk S).comp
    ((placesIdele S).coprod (AddMonoidHom.toMultiplicativeLeft (divisorIdele S)))
end
end GroundTheory.ProfCoh


