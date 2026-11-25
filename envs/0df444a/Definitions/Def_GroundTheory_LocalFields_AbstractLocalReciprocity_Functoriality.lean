-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Functoriality
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_Functoriality
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:34:39.687818+00:00
-- url     : https://prove2.me/theorems/472a6c5b-4219-5ce2-b868-fe8a1b4ab134
-- title:
--   Functoriality
-- statement:
--   Definitions and structural lemmas for Functoriality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relInertiaDegree_ne_zero
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_inertiaDegree_eq_mul
import Theorems.Thm_GroundTheory_LocalField_Abstract_norm_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_smul_mem_fixedModule
import Theorems.Thm_GroundTheory_LocalField_Abstract_smul_norm
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
section Conj
variable {G : Type*} [Group G]
theorem map_conj_apply {M : Type*} [CommGroup M] (f : G →* M) (σ x : G) :
    f (σ * x * σ⁻¹) = f x := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
theorem mem_map_conj {H : Subgroup G} {σ x : G} :
    x ∈ H.map (MulAut.conj σ).toMonoidHom ↔ σ⁻¹ * x * σ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨σ⁻¹ * x * σ, h, by simp [mul_assoc]⟩
theorem coe_map_conj (H : Subgroup G) (σ : G) :
    (H.map (MulAut.conj σ).toMonoidHom : Set G) = (fun x => σ⁻¹ * x * σ) ⁻¹' (H : Set G) := by
  ext x
  exact mem_map_conj
theorem inertiaDegree_map_conj (d : G →* Multiplicative ℤ̂) (K : Subgroup G) (σ : G) :
    inertiaDegree d (K.map (MulAut.conj σ).toMonoidHom) = inertiaDegree d K := by
  have h : d.comp (MulAut.conj σ).toMonoidHom = d := MonoidHom.ext fun x => map_conj_apply d σ x
  rw [inertiaDegree, inertiaDegree, Subgroup.map_map, h]
variable [TopologicalSpace G] [IsTopologicalGroup G]
def conjOpen (σ : G) (K : OpenSubgroup G) : OpenSubgroup G where
  toSubgroup := (K : Subgroup G).map (MulAut.conj σ).toMonoidHom
  isOpen' := by
    show IsOpen (((K : Subgroup G).map (MulAut.conj σ).toMonoidHom : Subgroup G) : Set G)
    rw [coe_map_conj]
    exact K.isOpen.preimage ((continuous_const.mul continuous_id).mul continuous_const)
theorem coe_conjOpen (σ : G) (K : OpenSubgroup G) :
    ((conjOpen σ K : OpenSubgroup G) : Subgroup G) = (K : Subgroup G).map (MulAut.conj σ).toMonoidHom :=
  rfl
theorem mem_conjOpen {σ x : G} {K : OpenSubgroup G} :
    x ∈ ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ↔ σ⁻¹ * x * σ ∈ (K : Subgroup G) :=
  mem_map_conj
theorem conjOpen_mono (σ : G) {K L : OpenSubgroup G} (h : L ≤ K) : conjOpen σ L ≤ conjOpen σ K :=
  fun _ hx => Subgroup.map_mono (f := (MulAut.conj σ).toMonoidHom) h hx
instance normal_conjOpen (σ : G) (K L : OpenSubgroup G) [hN : ((L : Subgroup G).subgroupOf K).Normal] :
    (((conjOpen σ L : OpenSubgroup G) : Subgroup G).subgroupOf (conjOpen σ K)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf, mem_conjOpen] at hn ⊢
  have hnK : σ⁻¹ * (n : G) * σ ∈ (K : Subgroup G) := mem_conjOpen.1 n.2
  have hgK : σ⁻¹ * (g : G) * σ ∈ (K : Subgroup G) := mem_conjOpen.1 g.2
  have := hN.conj_mem ⟨_, hnK⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨_, hgK⟩
  rw [Subgroup.mem_subgroupOf] at this
  convert this using 1
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  group
end Conj
section Maps
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A]
def galRestrict {K L K' L' : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L) :
    (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K' →* (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K :=
  QuotientGroup.map _ _ (Subgroup.inclusion hK) fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hL (Subgroup.mem_subgroupOf.1 hx)
noncomputable def normTateZero {K L K' L' : OpenSubgroup G} (hK : K' ≤ K) (hL : L' ≤ L)
    (hL'K' : L' ≤ K') (hLK : L ≤ K) :
    tateZero A (K' : Subgroup G) (L' : Subgroup G) →* tateZero A (K : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.map _ _ (norm A (K : Subgroup G) (K' : Subgroup G)) (by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_comap, norm_norm (M := (L' : Subgroup G)) hL'K' hK,
      ← norm_norm (M := (L' : Subgroup G)) hL hLK]
    exact ⟨_, rfl⟩)
noncomputable def galConj (σ : G) (K L : OpenSubgroup G) [((L : Subgroup G).subgroupOf K).Normal] :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K →*
      ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ⧸
        ((conjOpen σ L : OpenSubgroup G) : Subgroup G).subgroupOf (conjOpen σ K) :=
  QuotientGroup.map _ _
    ((K : Subgroup G).equivMapOfInjective _ (MulAut.conj σ).injective).toMonoidHom fun x hx => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact ⟨x, Subgroup.mem_subgroupOf.1 hx, rfl⟩
def conjFixed (σ : G) (K : OpenSubgroup G) :
    fixedModule A (K : Subgroup G) →* fixedModule A ((conjOpen σ K : OpenSubgroup G) : Subgroup G) where
  toFun a := ⟨σ • (a : A), smul_mem_fixedModule a.2 σ⟩
  map_one' := Subtype.ext (smul_one σ)
  map_mul' a b := Subtype.ext (smul_mul' σ (a : A) b)
theorem smul_norm_conjOpen (σ : G) (K L : OpenSubgroup G) (a : fixedModule A (L : Subgroup G)) :
    σ • (norm A (K : Subgroup G) (L : Subgroup G) a : A) =
      norm A ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ((conjOpen σ L : OpenSubgroup G) : Subgroup G)
        (conjFixed σ L a) := by
  have : (((L : Subgroup G).map (MulAut.conj σ).toMonoidHom).subgroupOf
      ((K : Subgroup G).map (MulAut.conj σ).toMonoidHom)).FiniteIndex :=
    (inferInstance : (((conjOpen σ L : OpenSubgroup G) : Subgroup G).subgroupOf
      (conjOpen σ K)).FiniteIndex)
  exact smul_norm σ a
noncomputable def tateZeroConj (σ : G) (K L : OpenSubgroup G) :
    tateZero A (K : Subgroup G) (L : Subgroup G) →*
      tateZero A ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ((conjOpen σ L : OpenSubgroup G) : Subgroup G) :=
  QuotientGroup.map _ _ (conjFixed σ K) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨conjFixed σ L b, Subtype.ext (smul_norm_conjOpen σ K L b).symm⟩)
end Maps
namespace ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] {D : ClassFieldData G A}
variable [TotallyDisconnectedSpace G]
section Restriction
noncomputable def FrobeniusLift.toBase {K K' : OpenSubgroup G} (hK : K' ≤ K) (s : D.FrobeniusLift K') :
    D.FrobeniusLift K where
  elt := s.elt
  mem := hK s.mem
  deg := s.deg * relInertiaDegree D.deg K K'
  deg_pos := Nat.mul_pos s.deg_pos (Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hK))
  deg_eq := by
    rw [s.deg_eq, inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G))
      (L := (K' : Subgroup G)) hK, Nat.mul_assoc]
end Restriction
section Conjugation
def FrobeniusLift.conj (ρ : G) {K : OpenSubgroup G} (s : D.FrobeniusLift K) :
    D.FrobeniusLift (conjOpen ρ K) where
  elt := ρ * s.elt * ρ⁻¹
  mem := ⟨s.elt, s.mem, rfl⟩
  deg := s.deg
  deg_pos := s.deg_pos
  deg_eq := by
    rw [map_conj_apply, s.deg_eq, coe_conjOpen, inertiaDegree_map_conj]
end Conjugation
end ClassFieldData
end GroundTheory.LocalField.Abstract


