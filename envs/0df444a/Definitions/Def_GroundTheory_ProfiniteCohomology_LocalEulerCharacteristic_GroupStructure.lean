-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
-- name    : GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:49.820797+00:00
-- url     : https://prove2.me/theorems/43acbd32-455f-4fb1-8370-31be29c442a2
-- title:
--   Group Structure
-- statement:
--   Definitions and structural lemmas for Group Structure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Theorems.Thm_GroundTheory_LocalField_lowerRamificationGroup_zero
import Theorems.Thm_GroundTheory_LocalField_ramificationQuotientToUnits_mk
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
attribute [local simp] GroundTheory.LocalField.ramificationQuotientToUnits_mk
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
section Parts
variable {Q Q' : Type*} [Group Q] [Group Q']
theorem map_coprimePart_le (p : ℕ) (f : Q →* Q') :
    (coprimePart p Q).map f ≤ coprimePart p Q' := by
  rw [coprimePart, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.subset_closure (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd f x) hx)
instance coprimePart_normal (p : ℕ) : (coprimePart p Q).Normal where
  conj_mem x hx g := by
    simpa using map_coprimePart_le p (MulAut.conj g).toMonoidHom (Subgroup.mem_map_of_mem _ hx)
instance primaryPart_normal (p : ℕ) : (primaryPart p Q).Normal where
  conj_mem x hx g := by
    have h : (primaryPart p Q).map (MulAut.conj g).toMonoidHom ≤ primaryPart p Q := by
      rw [primaryPart, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, ⟨n, hy⟩, rfl⟩
      exact Subgroup.subset_closure ⟨n, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hy]⟩
    simpa using h (Subgroup.mem_map_of_mem _ hx)
end Parts
section LemmaG
variable {G : Type*} [Group G]
variable (N : Subgroup G) [N.Normal]
instance coprimeQuotientPreimage_normal (p : ℕ) : (coprimeQuotientPreimage N p).Normal :=
  (coprimePart_normal p).comap _
instance primaryQuotientPreimage_normal (p : ℕ) : (primaryQuotientPreimage N p).Normal :=
  (primaryPart_normal p).comap _
section Relative
variable (G₀ G₁ : Subgroup G) [G₁.Normal]
theorem mem_coprimeRelPreimage_iff {p : ℕ} {x : G} :
    x ∈ coprimeRelPreimage G₀ G₁ p ↔ ∃ hx : x ∈ G₀,
      (QuotientGroup.mk (⟨x, hx⟩ : G₀) : G₀ ⧸ G₁.subgroupOf G₀) ∈ coprimePart p _ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩
instance coprimeRelPreimage_normal [G₀.Normal] (p : ℕ) : (coprimeRelPreimage G₀ G₁ p).Normal where
  conj_mem x hx g := by
    rw [mem_coprimeRelPreimage_iff] at hx ⊢
    obtain ⟨hx0, hx⟩ := hx
    let c : G₀ →* G₀ :=
      { toFun := fun y ↦ ⟨g * y * g⁻¹, (inferInstance : G₀.Normal).conj_mem y y.2 g⟩
        map_one' := by ext; simp
        map_mul' := fun a b ↦ by
          ext
          simp only [Subgroup.coe_mul]
          group }
    have hc : G₁.subgroupOf G₀ ≤ (G₁.subgroupOf G₀).comap c := fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact (inferInstance : G₁.Normal).conj_mem _ hy g
    exact ⟨(inferInstance : G₀.Normal).conj_mem x hx0 g,
      map_coprimePart_le p (QuotientGroup.map _ _ c hc) (Subgroup.mem_map_of_mem _ hx)⟩
variable [G₀.Normal]
end Relative
end LemmaG
section Galois
open GroundTheory.LocalField ValuativeRel IntermediateField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
instance isCyclic_quotient_lowerRamificationGroup_zero :
    IsCyclic ((L ≃ₐ[K] L) ⧸ lowerRamificationGroup K L 0) := by
  have : IsCyclic ((L ≃ₐ[K] L) ⧸ (residueAlgEquiv K L).ker) :=
    isCyclic_of_injective (QuotientGroup.kerLift _) (QuotientGroup.kerLift_injective _)
  exact isCyclic_of_surjective
    (QuotientGroup.quotientMulEquivOfEq (lowerRamificationGroup_zero K L).symm).toMonoidHom
    (MulEquiv.surjective _)
end Galois
end GroundTheory.ProfCoh


