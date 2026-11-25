-- Prove2me | Definitions.Def_GroundTheory_LocalFields_WeilGroupDefs
-- name    : GroundTheory_LocalFields_WeilGroupDefs
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:26.675971+00:00
-- url     : https://prove2.me/theorems/b9429c82-cacd-5888-9fa3-48ba2475da96
-- title:
--   Weil Group Defs
-- statement:
--   Definitions and structural lemmas for Weil Group Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_maximalUnramifiedExtensionGaloisEquiv_apply
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_unramifiedDegree_maximalUnramifiedExtensionFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk
attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply
attribute [local simp] GroundTheory.LocalField.maximalUnramifiedExtensionGaloisEquiv_apply
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract Topology
section Frobenius
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
theorem unramifiedDegree_maximalUnramifiedExtensionFrobenius_zpow (n : ℤ) :
    unramifiedDegree K (maximalUnramifiedExtension K Ω) (maximalUnramifiedExtensionFrobenius K Ω ^ n) =
      Multiplicative.ofAdd (n : ℤ̂) := by
  rw [map_zpow, unramifiedDegree_maximalUnramifiedExtensionFrobenius, ← ofAdd_zsmul, zsmul_one]
theorem injective_zpow_maximalUnramifiedExtensionFrobenius :
    Function.Injective fun n : ℤ ↦ maximalUnramifiedExtensionFrobenius K Ω ^ n := by
  intro m n h
  have h' := congrArg (unramifiedDegree K (maximalUnramifiedExtension K Ω)) h
  simp only [unramifiedDegree_maximalUnramifiedExtensionFrobenius_zpow] at h'
  exact Int.cast_injective (Multiplicative.ofAdd.injective h')
def frobeniusZPowersEquiv :
    Multiplicative ℤ ≃* Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) :=
  MonoidHom.ofInjective (f := zpowersHom _ (maximalUnramifiedExtensionFrobenius K Ω))
    (fun _ _ h ↦ Multiplicative.toAdd.injective
      (injective_zpow_maximalUnramifiedExtensionFrobenius K Ω h))
@[simp]
theorem coe_frobeniusZPowersEquiv (n : Multiplicative ℤ) :
    (frobeniusZPowersEquiv K Ω n : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) =
      maximalUnramifiedExtensionFrobenius K Ω ^ n.toAdd :=
  rfl
end Frobenius
section Weil
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
def weilSubgroup : Subgroup (Ω ≃ₐ[K] Ω) :=
  (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω)).comap
    (AlgEquiv.restrictNormalHom (maximalUnramifiedExtension K Ω))
variable {K Ω} in

theorem mem_weilSubgroup_iff {σ : Ω ≃ₐ[K] Ω} :
    σ ∈ weilSubgroup K Ω ↔ ∃ n : ℤ,
      σ.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω ^ n := by
  simp only [weilSubgroup, Subgroup.mem_comap, Subgroup.mem_zpowers_iff]
  exact exists_congr fun n ↦ eq_comm
theorem fixingSubgroup_le_weilSubgroup :
    (maximalUnramifiedExtension K Ω).fixingSubgroup ≤ weilSubgroup K Ω := by
  intro σ hσ
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker] at hσ
  exact mem_weilSubgroup_iff.2 ⟨0, by rw [zpow_zero]; exact hσ⟩
def WeilGroup : Type _ := weilSubgroup K Ω
namespace WeilGroup
instance : Group (WeilGroup K Ω) := inferInstanceAs (Group (weilSubgroup K Ω))
def toGal : WeilGroup K Ω →* (Ω ≃ₐ[K] Ω) := (weilSubgroup K Ω).subtype
theorem toGal_injective : Function.Injective (toGal K Ω) := Subtype.val_injective
variable {K Ω} in

def mk (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ weilSubgroup K Ω) : WeilGroup K Ω := ⟨σ, hσ⟩
def restrictFrobenius : WeilGroup K Ω →* Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) :=
  ((AlgEquiv.restrictNormalHom (maximalUnramifiedExtension K Ω)).comp (toGal K Ω)).codRestrict _
    fun σ ↦ σ.2
def degree : WeilGroup K Ω →* Multiplicative ℤ :=
  (frobeniusZPowersEquiv K Ω).symm.toMonoidHom.comp (restrictFrobenius K Ω)
variable {K Ω}
theorem restrictNormal_toGal (σ : WeilGroup K Ω) :
    (toGal K Ω σ).restrictNormal (maximalUnramifiedExtension K Ω) =
      maximalUnramifiedExtensionFrobenius K Ω ^ (degree K Ω σ).toAdd := by
  have h := (frobeniusZPowersEquiv K Ω).apply_symm_apply (restrictFrobenius K Ω σ)
  have h' := congrArg Subtype.val h
  rw [coe_frobeniusZPowersEquiv] at h'
  exact h'.symm
theorem degree_eq_iff (σ : WeilGroup K Ω) (n : ℤ) :
    degree K Ω σ = Multiplicative.ofAdd n ↔
      (toGal K Ω σ).restrictNormal (maximalUnramifiedExtension K Ω) =
        maximalUnramifiedExtensionFrobenius K Ω ^ n := by
  rw [restrictNormal_toGal]
  exact ⟨fun h ↦ by rw [h, toAdd_ofAdd], fun h ↦
    Multiplicative.toAdd.injective (injective_zpow_maximalUnramifiedExtensionFrobenius K Ω h)⟩
variable (K Ω) in

def inertia : Subgroup (WeilGroup K Ω) := (degree K Ω).ker
theorem mem_inertia_iff {σ : WeilGroup K Ω} :
    σ ∈ inertia K Ω ↔ toGal K Ω σ ∈ (maximalUnramifiedExtension K Ω).fixingSubgroup := by
  rw [inertia, MonoidHom.mem_ker, ← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker,
    AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, ← ofAdd_zero, degree_eq_iff, zpow_zero]
variable (K Ω) in

def toGalProd : WeilGroup K Ω →* (Ω ≃ₐ[K] Ω) × Multiplicative ℤ := (toGal K Ω).prod (degree K Ω)
variable (K Ω) in

instance instTopologicalSpace : TopologicalSpace (WeilGroup K Ω) :=
  TopologicalSpace.induced (toGalProd K Ω) inferInstance
theorem isInducing_toGalProd : IsInducing (toGalProd K Ω) := ⟨rfl⟩
theorem isEmbedding_toGalProd : IsEmbedding (toGalProd K Ω) :=
  ⟨isInducing_toGalProd, fun _ _ h ↦ toGal_injective K Ω (congrArg Prod.fst h)⟩
instance : IsTopologicalGroup (WeilGroup K Ω) :=
  isInducing_toGalProd.topologicalGroup (toGalProd K Ω)
instance : T2Space (WeilGroup K Ω) :=
  have : T2Space (Ω ≃ₐ[K] Ω) := krullTopology_t2
  isEmbedding_toGalProd.t2Space
theorem continuous_toGal : Continuous (toGal K Ω) :=
  continuous_fst.comp isInducing_toGalProd.continuous
theorem continuous_degree : Continuous (degree K Ω) :=
  continuous_snd.comp isInducing_toGalProd.continuous
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → WeilGroup K Ω} :
    Continuous f ↔ Continuous (toGal K Ω ∘ f) ∧ Continuous (degree K Ω ∘ f) := by
  rw [isInducing_toGalProd.continuous_iff, continuous_prodMk]
  rfl
theorem isOpen_inertia : IsOpen (inertia K Ω : Set (WeilGroup K Ω)) :=
  (isOpen_discrete ({1} : Set (Multiplicative ℤ))).preimage continuous_degree
variable (K Ω) in

def inertiaEquiv : inertia K Ω ≃ₜ* (maximalUnramifiedExtension K Ω).fixingSubgroup where
  toFun σ := ⟨toGal K Ω σ, mem_inertia_iff.1 σ.2⟩
  invFun τ := ⟨mk τ (fixingSubgroup_le_weilSubgroup K Ω τ.2), mem_inertia_iff.2 τ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_toGal.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    have hc : Continuous fun τ : (maximalUnramifiedExtension K Ω).fixingSubgroup ↦
        mk (τ : Ω ≃ₐ[K] Ω) (fixingSubgroup_le_weilSubgroup K Ω τ.2) := by
      refine (continuous_iff (K := K) (Ω := Ω)).2 ⟨continuous_subtype_val, ?_⟩
      have : (degree K Ω ∘ fun τ : (maximalUnramifiedExtension K Ω).fixingSubgroup ↦
          mk (τ : Ω ≃ₐ[K] Ω) (fixingSubgroup_le_weilSubgroup K Ω τ.2)) = fun _ ↦ 1 :=
        funext fun τ ↦ (mem_inertia_iff (σ := mk _ (fixingSubgroup_le_weilSubgroup K Ω τ.2))).2 τ.2
      rw [this]
      exact continuous_const
    exact hc.subtype_mk _
instance : CompactSpace (inertia K Ω) :=
  have : CompactSpace (maximalUnramifiedExtension K Ω).fixingSubgroup :=
    isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed (k := K) (K := Ω) (maximalUnramifiedExtension K Ω)).isCompact
  (inertiaEquiv K Ω).toHomeomorph.symm.compactSpace
theorem isCompact_inertia : IsCompact (inertia K Ω : Set (WeilGroup K Ω)) :=
  isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (inertia K Ω)))
instance : LocallyCompactSpace (WeilGroup K Ω) :=
  isCompact_inertia.locallyCompactSpace_of_mem_nhds_of_group
    (isOpen_inertia.mem_nhds (Subgroup.one_mem _))
end WeilGroup
end Weil
end GroundTheory.LocalField


