-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
-- name    : GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:34.818019+00:00
-- url     : https://prove2.me/theorems/3092269a-c50f-4a75-9467-d2b3aea2e326
-- title:
--   Fixed Field
-- statement:
--   Definitions and structural lemmas for Fixed Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisModules/FixedField.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21


set_option autoImplicit false
namespace GroundTheory.ProfCoh
open IntermediateField InfiniteGalois
universe u
variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]
section FixingSubgroup
theorem isOpen_fixingSubgroup_finiteGalois (E : FiniteGaloisIntermediateField K L) :
    IsOpen (E.fixingSubgroup : Set Gal(L/K)) :=
  fixingSubgroup_isOpen E.toIntermediateField
theorem normal_fixingSubgroup_finiteGalois [IsGalois K L] (E : FiniteGaloisIntermediateField K L) :
    E.fixingSubgroup.Normal :=
  (normal_iff_isGalois E.toIntermediateField).2 E.isGalois
variable [IsGalois K L]
def fixingOpenNormalSubgroup (E : FiniteGaloisIntermediateField K L) :
    OpenNormalSubgroup Gal(L/K) where
  toSubgroup := E.fixingSubgroup
  isOpen' := isOpen_fixingSubgroup_finiteGalois E
  isNormal' := normal_fixingSubgroup_finiteGalois E
@[simp]
theorem coe_fixingOpenNormalSubgroup
    (E : FiniteGaloisIntermediateField K L) :
    (fixingOpenNormalSubgroup E : Subgroup Gal(L/K)) = E.fixingSubgroup :=
  rfl
end FixingSubgroup
section FixedField
variable [IsGalois K L] (U : OpenNormalSubgroup Gal(L/K))
def openNormalToClosed : ClosedSubgroup Gal(L/K) :=
  ⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩
instance : (openNormalToClosed U).Normal :=
  U.isNormal'
@[simp]
theorem fixingSubgroup_fixedField_openNormalSubgroup :
    (fixedField (U : Subgroup Gal(L/K))).fixingSubgroup = U :=
  fixingSubgroup_fixedField (openNormalToClosed U)
instance finiteDimensional_fixedField_openNormalSubgroup :
    FiniteDimensional K (fixedField (U : Subgroup Gal(L/K))) := by
  refine (isOpen_iff_finite _).1 ?_
  rw [fixingSubgroup_fixedField_openNormalSubgroup]
  exact U.isOpen
instance isGalois_fixedField_openNormalSubgroup :
    IsGalois K (fixedField (U : Subgroup Gal(L/K))) := by
  refine (normal_iff_isGalois _).1 ?_
  rw [fixingSubgroup_fixedField_openNormalSubgroup]
  exact U.isNormal'
noncomputable def fixedFiniteGalois : FiniteGaloisIntermediateField K L where
  toIntermediateField := fixedField (U : Subgroup Gal(L/K))
@[simp]
theorem fixedFiniteGalois_toIntermediateField :
    (fixedFiniteGalois U).toIntermediateField = fixedField (U : Subgroup Gal(L/K)) :=
  rfl
noncomputable def quotientEquivGal :
    Gal(L/K) ⧸ (U : Subgroup Gal(L/K)) ≃* Gal(fixedField (U : Subgroup Gal(L/K))/K) :=
  normalAutEquivQuotient (openNormalToClosed U)
@[simp]
theorem quotientEquivGal_mk_apply (σ : Gal(L/K)) (x : fixedField (U : Subgroup Gal(L/K))) :
    ((quotientEquivGal U (σ : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) x : _) : L) = σ x :=
  AlgEquiv.restrictNormal_commutes σ _ x
omit [IsGalois K L] in

theorem mem_invariants_galAdd_iff (x : L) :
    x ∈ Representation.invariants ((galAdd K L).ρ.comp (U : Subgroup Gal(L/K)).subtype) ↔
      x ∈ fixedField (U : Subgroup Gal(L/K)) :=
  ⟨fun h σ => h σ, fun h σ => h σ⟩
omit [IsGalois K L] in

def invariantsGalAddEquiv :
    Representation.invariants ((galAdd K L).ρ.comp (U : Subgroup Gal(L/K)).subtype) ≃ₗ[K]
      fixedField (U : Subgroup Gal(L/K)) where
  toFun x := ⟨x.1, (mem_invariants_galAdd_iff U x.1).1 x.2⟩
  invFun x := ⟨x.1, (mem_invariants_galAdd_iff U x.1).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
end FixedField
section Correspondence
variable [IsGalois K L]
@[simp]
theorem fixingOpenNormalSubgroup_fixedFiniteGalois
    (U : OpenNormalSubgroup Gal(L/K)) : fixingOpenNormalSubgroup (fixedFiniteGalois U) = U := by
  ext σ
  change σ ∈ (fixedField (U : Subgroup Gal(L/K))).fixingSubgroup ↔ σ ∈ (U : Subgroup Gal(L/K))
  rw [fixingSubgroup_fixedField_openNormalSubgroup]
@[simp]
theorem fixedFiniteGalois_fixingOpenNormalSubgroup
    (E : FiniteGaloisIntermediateField K L) : fixedFiniteGalois (fixingOpenNormalSubgroup E) = E :=
  FiniteGaloisIntermediateField.val_injective (fixedField_fixingSubgroup E.toIntermediateField)
noncomputable def openNormalSubgroupEquiv :
    OpenNormalSubgroup Gal(L/K) ≃o (FiniteGaloisIntermediateField K L)ᵒᵈ where
  toFun U := OrderDual.toDual (fixedFiniteGalois U)
  invFun E := fixingOpenNormalSubgroup (OrderDual.ofDual E)
  left_inv U := fixingOpenNormalSubgroup_fixedFiniteGalois U
  right_inv E := fixedFiniteGalois_fixingOpenNormalSubgroup (OrderDual.ofDual E)
  map_rel_iff' {U V} := by
    change fixedField (V : Subgroup Gal(L/K)) ≤ fixedField (U : Subgroup Gal(L/K)) ↔ U ≤ V
    rw [le_iff_le, fixingSubgroup_fixedField_openNormalSubgroup]
    exact Iff.rfl
end Correspondence
section Cofinal
variable [IsGalois K L]
end Cofinal
end GroundTheory.ProfCoh


