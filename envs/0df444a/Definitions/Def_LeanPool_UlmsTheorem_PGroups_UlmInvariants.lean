-- Prove2me | Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
-- name    : LeanPool_UlmsTheorem_PGroups_UlmInvariants
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:55:40.58533+00:00
-- url     : https://prove2.me/theorems/43b57ba0-1eb1-4e8b-9608-21f84c10ae15
-- title:
--   Ulm Invariants
-- statement:
--   Definitions and structural lemmas for Ulm Invariants, from Elan Roth; LeanPool contributors's pinned Ulm’s theorem for abelian p-groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmInvariants.lean

module
public import Mathlib.Algebra.Field.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_antitone
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_succ
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace UlmsTheorem
open Ordinal Cardinal
variable (p : ℕ) [hp : Fact p.Prime]
noncomputable def layerSuccIncl {G : Type*} [AddCommGroup G] (α : Ordinal) :
    ulmSubgroup p (Order.succ α) (G := G) →+ ulmSubgroup p α (G := G) := by
  refine AddSubgroup.subtype _ |>.codRestrict _ ?_
  intro x
  exact ulmSubgroup_antitone p (Order.le_succ α) x.property
noncomputable def layerQuotient {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Type _ :=
  (ulmSubgroup p α (G := G)) ⧸
    ((ulmSubgroup p (Order.succ α) (G := G)).comap
      (ulmSubgroup p α (G := G)).subtype)
noncomputable instance {G : Type*} [AddCommGroup G] (α : Ordinal) :
    AddCommGroup (layerQuotient p α (G := G)) := by
  unfold layerQuotient
  infer_instance
omit hp in
/-- Every element of `G_α / G_{α+1}` has order `p`. -/
lemma layerQuotient_orderOf_dvd_p {G : Type*} [AddCommGroup G] (α : Ordinal)
    (x : layerQuotient p α (G := G)) : p • x = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  change QuotientAddGroup.mk'
      ((ulmSubgroup p (Order.succ α) (G := G)).comap (ulmSubgroup p α (G := G)).subtype)
      (p • a) =
    QuotientAddGroup.mk'
      ((ulmSubgroup p (Order.succ α) (G := G)).comap (ulmSubgroup p α (G := G)).subtype)
      0
  have hmem : (p • (a : G)) ∈ ulmSubgroup p (Order.succ α) (G := G) := by
    rw [ulmSubgroup_succ]
    exact ⟨a, a.property, rfl⟩
  apply (QuotientAddGroup.mk'_eq_mk' _).2
  refine ⟨-(p • a), ?_, by simp⟩
  exact (ulmSubgroup p (Order.succ α) (G := G)).neg_mem hmem
noncomputable instance layerQuotientModule {G : Type*} [AddCommGroup G]
    (α : Ordinal) : Module (ZMod p) (layerQuotient p α (G := G)) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := layerQuotient p α (G := G)) ?_
  intro x
  simpa using layerQuotient_orderOf_dvd_p p α x
noncomputable def layerInvariant {G : Type*} [AddCommGroup G]
    (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (layerQuotient p α (G := G))
noncomputable def ulmDenSubmodule {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Submodule (ZMod p) (pSocleAt p α (G := G)) :=
  AddSubgroup.toZModSubmodule p (pSocleAtSuccSubgroupOf p α)
abbrev ulmQuotient {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Type _ :=
  (pSocleAt p α (G := G)) ⧸ ulmDenSubmodule p α
noncomputable def ulmInvariant {G : Type*} [AddCommGroup G]
    (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (ulmQuotient p α (G := G))
section RelativeInvariants
variable {G : Type*} [AddCommGroup G]
noncomputable def markedGradedDen (S : AddSubgroup G) (α : Ordinal) :
    AddSubgroup (pSocleAt p α (G := G)) :=
  (pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α)).comap
    (pSocleAt p α).subtype
noncomputable def markedGradedSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (pSocleAt p α (G := G)) :=
  AddSubgroup.toZModSubmodule p (markedGradedDen p S α)
abbrev markedGradedQuotient (S : AddSubgroup G) (α : Ordinal) : Type _ :=
  (pSocleAt p α (G := G)) ⧸ markedGradedSubmodule p S α
noncomputable def markedGradedInvariant (S : AddSubgroup G) (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (markedGradedQuotient p S α)
noncomputable def hillDen (S : AddSubgroup G) (α : Ordinal) :
    AddSubgroup (pSocleAt p α (G := G)) :=
  (pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))).comap
    (pSocleAt p α).subtype
noncomputable def hillSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (pSocleAt p α (G := G)) :=
  AddSubgroup.toZModSubmodule p (hillDen p S α)
abbrev hillQuotient (S : AddSubgroup G) (α : Ordinal) : Type _ :=
  (pSocleAt p α (G := G)) ⧸ hillSubmodule p S α
noncomputable def hillInvariant (S : AddSubgroup G) (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (hillQuotient p S α)
noncomputable abbrev relativeUlmDen (S : AddSubgroup G) (α : Ordinal) :=
  hillDen p S α
noncomputable abbrev relativeUlmSubmodule (S : AddSubgroup G) (α : Ordinal) :=
  hillSubmodule p S α
abbrev relativeUlmQuotient (S : AddSubgroup G) (α : Ordinal) :=
  hillQuotient p S α
noncomputable abbrev relativeUlmInvariant (S : AddSubgroup G) (α : Ordinal) :=
  hillInvariant p S α
lemma markedGradedSubmodule_le_hillSubmodule (S : AddSubgroup G) (α : Ordinal) :
    markedGradedSubmodule p S α ≤ hillSubmodule p S α := by
  intro x hx
  change (x : G) ∈ pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))
  change (x : G) ∈
    pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α) at hx
  refine ⟨x.property, ?_⟩
  have hle :
      pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α) ≤
        S ⊔ ulmSubgroup p (Order.succ α) := by
    apply sup_le
    · intro y hy
      exact AddSubgroup.mem_sup_right hy.2
    · intro y hy
      exact AddSubgroup.mem_sup_left hy.1
  exact hle hx
lemma ulmDenSubmodule_le_hillSubmodule (S : AddSubgroup G) (α : Ordinal) :
    ulmDenSubmodule p α ≤ hillSubmodule p S α := by
  intro x hx
  change (x : G) ∈ pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))
  change (x : G) ∈ pSocleAt p (Order.succ α) at hx
  exact ⟨x.property, AddSubgroup.mem_sup_right hx.2⟩
noncomputable def relativeOccupiedSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (ulmQuotient p α (G := G)) :=
  (hillSubmodule p S α).map (ulmDenSubmodule p α).mkQ
noncomputable def occupiedQuotientEquivRelative (S : AddSubgroup G) (α : Ordinal) :
    (ulmQuotient p α (G := G) ⧸ relativeOccupiedSubmodule p S α) ≃ₗ[ZMod p]
      hillQuotient p S α :=
  Submodule.quotientQuotientEquivQuotient
    (ulmDenSubmodule p α) (hillSubmodule p S α)
    (ulmDenSubmodule_le_hillSubmodule p S α)
noncomputable def overhangSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (markedGradedQuotient p S α) :=
  (hillSubmodule p S α).map (markedGradedSubmodule p S α).mkQ
noncomputable def overhangInvariant (S : AddSubgroup G) (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (overhangSubmodule (p := p) S α)
noncomputable def markedGradedToHill (S : AddSubgroup G) (α : Ordinal) :
    markedGradedQuotient p S α →ₗ[ZMod p] hillQuotient p S α :=
  Submodule.factor (markedGradedSubmodule_le_hillSubmodule p S α)
end RelativeInvariants
noncomputable def ulmLength {G : Type*} [AddCommGroup G] : Ordinal.{0} :=
  sInf {α : Ordinal.{0} | ulmSubgroup p α (G := G) = ⊥}
namespace ulmLength
variable {G : Type*} [AddCommGroup G]
end ulmLength
noncomputable def tailInvariants {G : Type*} [AddCommGroup G]
    (γ : Ordinal) (n : ℕ) : Fin n → Cardinal :=
  fun k ↦ ulmInvariant p (ω * γ + k.1) (G := G)
end UlmsTheorem


