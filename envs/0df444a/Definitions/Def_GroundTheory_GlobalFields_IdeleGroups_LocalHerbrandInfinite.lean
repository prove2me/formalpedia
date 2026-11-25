-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrandInfinite
-- name    : GroundTheory_GlobalFields_IdeleGroups_LocalHerbrandInfinite
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T07:23:16.026148+00:00
-- url     : https://prove2.me/theorems/73a83860-c2d8-5238-ba6a-a59f2d13a149
-- title:
--   Local Herbrand Infinite
-- statement:
--   Definitions and structural lemmas for Local Herbrand Infinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrandInfinite.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Theorems.Thm_GroundTheory_Global_coe_decomposition_smul_integerUnits
import Theorems.Thm_GroundTheory_Global_coe_decomposition_smul_integers
import Theorems.Thm_GroundTheory_Global_coe_decomposition_smul_units
import Theorems.Thm_GroundTheory_Global_coe_integerUnitsAddEquiv
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_decompositionMulEquiv_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
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
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.coe_decomposition_smul_integerUnits
attribute [local simp] GroundTheory.Global.coe_decomposition_smul_integers
attribute [local simp] GroundTheory.Global.coe_decomposition_smul_units
attribute [local simp] GroundTheory.Global.coe_integerUnitsAddEquiv
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.decompositionMulEquiv_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21


set_option autoImplicit false
noncomputable section
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion GroundTheory.GroupCoh
open scoped NumberField.LiesOver
namespace GroundTheory.Global
section NeZero
variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
end NeZero
section Action
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (w : InfinitePlace L)
theorem apply_algEquiv_of_mem_stabilizer {σ : Gal(L/K)}
    (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w) (x : L) : w (σ x) = w x := by
  have h := congrArg (fun u : InfinitePlace L ↦ u (σ x)) (MulAction.mem_stabilizer_iff.1 hσ)
  simp only [InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply] at h
  exact h.symm
def withAbsMapOf (σ : Gal(L/K)) : WithAbs w.1 →+* WithAbs w.1 :=
  WithAbs.map w.1 w.1 (σ : L →+* L)
theorem ofAbs_withAbsMapOf (σ : Gal(L/K)) (x : WithAbs w.1) :
    (withAbsMapOf w σ x).ofAbs = σ x.ofAbs :=
  rfl
variable {w}
theorem isometry_withAbsMapOf {σ : Gal(L/K)} (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w) :
    Isometry (withAbsMapOf w σ) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, ofAbs_withAbsMapOf]
    exact apply_algEquiv_of_mem_stabilizer w hσ x.ofAbs
def completionRingHomOf {σ : Gal(L/K)} (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w) :
    w.Completion →+* w.Completion :=
  ((Completion.equiv w).symm.toRingHom.comp (isometry_withAbsMapOf hσ).mapRingHom).comp
    (Completion.equiv w).toRingHom
theorem continuous_completionRingHomOf {σ : Gal(L/K)}
    (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w) : Continuous (completionRingHomOf hσ) :=
  (continuous_ofCompletion w).comp <|
    UniformSpace.Completion.continuous_map.comp (continuous_toCompletion w)
theorem completionRingHomOf_coe {σ : Gal(L/K)} (hσ : σ ∈ MulAction.stabilizer Gal(L/K) w)
    (x : WithAbs w.1) :
    completionRingHomOf hσ (x : w.Completion) = ((withAbsMapOf w σ x : WithAbs w.1) :
      w.Completion) :=
  Completion.ext <| (isometry_withAbsMapOf hσ).mapRingHom_coe x
variable (w) in

theorem ringHom_ext_completion {f g : w.Completion →+* w.Completion} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ x : WithAbs w.1, f (x : w.Completion) = g (x : w.Completion)) :
    f = g :=
  RingHom.ext (congrFun ((denseRange_coe w).equalizer hf hg (funext h)))
variable (w)
instance infiniteDecompositionMulSemiringAction :
    MulSemiringAction (MulAction.stabilizer Gal(L/K) w) w.Completion where
  smul σ x := completionRingHomOf σ.2 x
  one_smul x := by
    change completionRingHomOf (1 : MulAction.stabilizer Gal(L/K) w).2 x = RingHom.id _ x
    congr 1
    exact ringHom_ext_completion w (continuous_completionRingHomOf _) continuous_id fun y ↦ by
      rw [completionRingHomOf_coe]
      rfl
  mul_smul σ τ x := by
    change completionRingHomOf (σ * τ).2 x =
      ((completionRingHomOf σ.2).comp (completionRingHomOf τ.2)) x
    congr 1
    exact ringHom_ext_completion w (continuous_completionRingHomOf _)
      ((continuous_completionRingHomOf σ.2).comp (continuous_completionRingHomOf τ.2)) fun y ↦ by
        rw [RingHom.comp_apply, completionRingHomOf_coe, completionRingHomOf_coe,
          completionRingHomOf_coe]
        rfl
  smul_zero σ := map_zero _
  smul_add σ := map_add _
  smul_one σ := map_one _
  smul_mul σ := map_mul _
instance infiniteDecompositionUnitsAction :
    MulDistribMulAction (MulAction.stabilizer Gal(L/K) w) w.Completionˣ :=
  Units.mulDistribMulActionRight
variable {w}
theorem infiniteDecomposition_smul_coe (σ : MulAction.stabilizer Gal(L/K) w) (x : WithAbs w.1) :
    σ • (x : w.Completion) =
      ((withAbsMapOf w (σ : Gal(L/K)) x : WithAbs w.1) : w.Completion) :=
  completionRingHomOf_coe σ.2 x
theorem continuous_infiniteDecomposition_smul (σ : MulAction.stabilizer Gal(L/K) w) :
    Continuous fun x : w.Completion ↦ σ • x :=
  continuous_completionRingHomOf σ.2
end Action
section Local
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)
  (w : InfinitePlace L) [w.LiesOver v]
theorem infiniteDecomposition_smul_algebraMap (σ : MulAction.stabilizer Gal(L/K) w)
    (c : v.Completion) :
    σ • algebraMap v.Completion w.Completion c = algebraMap v.Completion w.Completion c := by
  have h := (denseRange_coe v).equalizer
    ((continuous_infiniteDecomposition_smul σ).comp
      (continuous_algebraMap v.Completion w.Completion))
    (continuous_algebraMap v.Completion w.Completion) (funext fun x ↦ ?_)
  · exact congrFun h c
  · simp only [Function.comp_apply]
    rw [Completion.algebraMap_coe, infiniteDecomposition_smul_coe]
    congr 2
    apply (WithAbs.equiv w.1).injective
    change σ.1 (algebraMap (WithAbs v.1) (WithAbs w.1) x).ofAbs =
      (algebraMap (WithAbs v.1) (WithAbs w.1) x).ofAbs
    rw [WithAbs.ofAbs_algebraMap, AlgEquiv.commutes]
def infiniteDecompositionAlgEquiv (σ : MulAction.stabilizer Gal(L/K) w) :
    Gal(w.Completion/v.Completion) :=
  AlgEquiv.ofRingEquiv (f := MulSemiringAction.toRingEquiv _ w.Completion σ)
    (infiniteDecomposition_smul_algebraMap v w σ)
@[simp]
theorem infiniteDecompositionAlgEquiv_apply (σ : MulAction.stabilizer Gal(L/K) w)
    (x : w.Completion) : infiniteDecompositionAlgEquiv v w σ x = σ • x :=
  rfl
def infiniteDecompositionToLocal :
    MulAction.stabilizer Gal(L/K) w →* Gal(w.Completion/v.Completion) where
  toFun := infiniteDecompositionAlgEquiv v w
  map_one' := AlgEquiv.ext fun x ↦ one_smul (MulAction.stabilizer Gal(L/K) w) x
  map_mul' σ τ := AlgEquiv.ext fun x ↦ mul_smul σ τ x
@[simp]
theorem infiniteDecompositionToLocal_apply (σ : MulAction.stabilizer Gal(L/K) w)
    (x : w.Completion) : infiniteDecompositionToLocal v w σ x = σ • x :=
  rfl
theorem infiniteDecompositionToLocal_injective :
    Function.Injective (infiniteDecompositionToLocal v w) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  have h := congrArg (fun f : Gal(w.Completion/v.Completion) ↦
    f ((WithAbs.toAbs w.1 x : WithAbs w.1) : w.Completion)) hσ
  simp only [AlgEquiv.one_apply] at h
  rw [infiniteDecompositionToLocal_apply, infiniteDecomposition_smul_coe] at h
  have h' := UniformSpace.Completion.coe_injective (WithAbs w.1)
    (congrArg Completion.toCompletion h)
  rw [OneMemClass.coe_one, AlgEquiv.one_apply]
  exact congrArg WithAbs.ofAbs h'
variable [IsGalois K L]
theorem natCard_infiniteDecompositionGroup :
    Nat.card (MulAction.stabilizer Gal(L/K) w) = Module.finrank v.Completion w.Completion := by
  rw [NumberField.InfinitePlace.card_stabilizer]
  by_cases h : w.IsUnramified K
  · rw [if_pos h, h.finrank_eq_one v]
  · rw [if_neg h, NumberField.InfinitePlace.IsRamified.finrank_eq_two v h]
theorem infiniteDecompositionToLocal_bijective :
    Function.Bijective (infiniteDecompositionToLocal v w) := by
  refine (infiniteDecompositionToLocal_injective v w).bijective_of_nat_card_le ?_
  rw [natCard_infiniteDecompositionGroup v w, InfinitePlace.natCard_gal_completion w]
def infiniteDecompositionMulEquiv :
    MulAction.stabilizer Gal(L/K) w ≃* Gal(w.Completion/v.Completion) :=
  MulEquiv.ofBijective (infiniteDecompositionToLocal v w)
    (infiniteDecompositionToLocal_bijective v w)
end Local
section Herbrand
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)
  (w : InfinitePlace L) [w.LiesOver v]
variable [IsGalois K L]
end Herbrand
end GroundTheory.Global


