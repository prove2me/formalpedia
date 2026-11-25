-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
-- name    : GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T08:02:39.174235+00:00
-- url     : https://prove2.me/theorems/d8d01c27-c041-4afd-bbcb-84ab29931a4e
-- title:
--   Congruence Subgroup Le Standard Open Subgroup
-- statement:
--   Definitions and structural lemmas for Congruence Subgroup Le Standard Open Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
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
open Topology Filter NumberField IsDedekindDomain WithZero Function
open scoped NumberField.AdeleRing
namespace GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
structure Modulus where

  ideal : Ideal (𝓞 K)
  ideal_ne_bot : ideal ≠ ⊥

  real : Set {w : InfinitePlace K // w.IsReal}
variable {K}
namespace IdeleGroup
def positiveAt (S : Set {w : InfinitePlace K // w.IsReal}) : Subgroup (IdeleGroup K) where
  carrier := {x | ∀ w ∈ S, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
    ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)}
  one_mem' w _ := by simp
  mul_mem' {a b} ha hb w hw := by
    rw [map_mul, Units.val_mul, map_mul]
    exact mul_pos (ha w hw) (hb w hw)
  inv_mem' {a} ha w hw := by
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_pos.2 (ha w hw)
end IdeleGroup
open IdeleGroup
namespace Modulus
variable (𝔪 : Modulus K)
def exponent (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  multiplicity v.asIdeal 𝔪.ideal
def congruenceSubgroup : Subgroup (IdeleGroup K) :=
  (idealLevel 𝔪.ideal).comap (toFinite K) ⊓ positiveAt 𝔪.real
def idelesOneMod : Subgroup (IdeleGroup K) :=
  (⨅ (v : HeightOneSpectrum (𝓞 K)) (_ : v.asIdeal ∣ 𝔪.ideal),
    (unitsLevel v (𝔪.exponent v)).comap (finiteProj v)) ⊓ positiveAt 𝔪.real
def rayUnits : Subgroup Kˣ :=
  𝔪.idelesOneMod.comap (diagonal K)
end Modulus
end
end GroundTheory.Global


