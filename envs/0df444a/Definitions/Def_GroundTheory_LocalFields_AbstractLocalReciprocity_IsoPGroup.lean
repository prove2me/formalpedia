-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoPGroup
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_IsoPGroup
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:43:30.064854+00:00
-- url     : https://prove2.me/theorems/787cd90f-fd83-5b5b-9c7c-be8ac8839df1
-- title:
--   Iso PGroup
-- statement:
--   Definitions and structural lemmas for Iso PGroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoPGroup.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoCyclic
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_mk_mem_range_galRestrict_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk


set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
open ProfiniteInteger
section Normal
variable {G : Type*} [Group G]
theorem normal_subgroupOf_of_le {K L M : Subgroup G} (hMK : M ≤ K) [hN : (L.subgroupOf K).Normal] :
    (L.subgroupOf M).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hN.conj_mem ⟨n, hMK n.2⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, hMK g.2⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h⟩
end Normal
section FixedField
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
def fixedOpen (H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G where
  toSubgroup := (H.comap (QuotientGroup.mk' _)).map (K : Subgroup G).subtype
  isOpen' := Subgroup.isOpen_mono (H₁ := (L : Subgroup G)) (fun x hx => ⟨⟨x, hLK hx⟩, by
      show ((⟨x, hLK hx⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈ H
      rw [(QuotientGroup.eq_one_iff (⟨x, hLK hx⟩ : (K : Subgroup G))).2 (Subgroup.mem_subgroupOf.2 hx)]
      exact H.one_mem, rfl⟩) L.isOpen
theorem mem_fixedOpen {H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)} {g : G} :
    g ∈ ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ↔
      ∃ h : g ∈ (K : Subgroup G), ((⟨g, h⟩ : (K : Subgroup G)) :
        (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈ H := by
  show g ∈ (H.comap (QuotientGroup.mk' _)).map (K : Subgroup G).subtype ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨h, hH⟩
    exact ⟨⟨g, h⟩, hH, rfl⟩
variable (H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
theorem le_fixedOpen : L ≤ fixedOpen hLK H := fun x hx =>
  (mem_fixedOpen hLK).2 ⟨hLK hx, by
    rw [(QuotientGroup.eq_one_iff (⟨x, hLK hx⟩ : (K : Subgroup G))).2 (Subgroup.mem_subgroupOf.2 hx)]
    exact H.one_mem⟩
theorem fixedOpen_le : fixedOpen hLK H ≤ K := fun _ hx => ((mem_fixedOpen hLK).1 hx).1
instance normal_fixedOpen_self :
    ((L : Subgroup G).subgroupOf ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G)).Normal :=
  normal_subgroupOf_of_le (K := (K : Subgroup G)) (fun _ hx => ((mem_fixedOpen hLK).1 hx).1)
instance normal_fixedOpen [hH : H.Normal] :
    (((fixedOpen hLK H : OpenSubgroup G) : Subgroup G).subgroupOf K).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨_, hnH⟩ := (mem_fixedOpen hLK).1 hn
    refine (mem_fixedOpen hLK).2 ⟨(g * n * g⁻¹).2, ?_⟩
    exact hH.conj_mem _ hnH (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)⟩
theorem range_galRestrict_fixedOpen [CompactSpace G] :
    (galRestrict (K := K) (L := L) (K' := fixedOpen hLK H) (L' := L) (fixedOpen_le hLK H)
      le_rfl).range = H := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [mk_mem_range_galRestrict_iff (le_fixedOpen hLK H) (fixedOpen_le hLK H), mem_fixedOpen]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨k.2, h⟩⟩
noncomputable def galFixedEquiv [CompactSpace G] :
    ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ⧸
      (L : Subgroup G).subgroupOf ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ≃* H :=
  (MonoidHom.ofInjective (galRestrict_injective (K := K) (L := L) (fixedOpen_le hLK H))).trans
    (MulEquiv.subgroupCongr (range_galRestrict_fixedOpen hLK H))
end FixedField
section Restrict
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
end Restrict
namespace ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
section Tower
variable {K M L : OpenSubgroup G} (hLM : L ≤ M) (hMK : M ≤ K)
  [((L : Subgroup G).subgroupOf K).Normal] [((L : Subgroup G).subgroupOf M).Normal]
  [((M : Subgroup G).subgroupOf K).Normal]
end Tower
section PGroup
end PGroup
end ClassFieldData
end GroundTheory.LocalField.Abstract


