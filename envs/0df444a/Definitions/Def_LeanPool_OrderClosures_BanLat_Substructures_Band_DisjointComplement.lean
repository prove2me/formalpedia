-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_DisjointComplement
-- name    : LeanPool_OrderClosures_BanLat_Substructures_Band_DisjointComplement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:29:45.882632+00:00
-- url     : https://prove2.me/theorems/2d1b0fd6-24a2-484a-9a85-e19b44f16580
-- title:
--   Disjoint Complement
-- statement:
--   Definitions and structural lemmas for Disjoint Complement, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
public import Theorems.Thm_IsVLDisjoint_add_left
public import Theorems.Thm_IsVLDisjoint_mono_left
public import Theorems.Thm_IsVLDisjoint_smul_left
public import Theorems.Thm_isLUB_inf_const
public import Theorems.Thm_isVLDisjoint_zero_left

set_option autoImplicit true
@[expose] public section
@[expose] public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
def disjointComplement (A : Set X) : Set X :=
  {x : X | ∀ a ∈ A, IsVLDisjoint x a}
@[inherit_doc]
postfix:max "ᵈ" => disjointComplement
namespace Band
def disjointComplement (A : Set X) : Band X :=
  Band.ofPosDirectedSSupMem
    (.ofSolid
      { carrier := Aᵈ
        add_mem' := fun {_ _} hx hy a ha => (hx a ha).add_left (hy a ha)
        zero_mem' := fun a _ => isVLDisjoint_zero_left a
        smul_mem' := fun c {_} hx a ha => (hx a ha).smul_left c }
      (fun _ _ hx hxy a ha => (hx a ha).mono_left hxy))
    (by
      intro S hSJ hpos _ hne y hy a ha
      have hy_nn : 0 ≤ y := by
        obtain ⟨s, hs⟩ := hne
        exact (hpos s hs).trans (hy.1 hs)
      have key : IsLUB ((fun z => |a| ⊓ z) '' S) (|a| ⊓ y) := isLUB_inf_const _ hy
      have hzero : ∀ s ∈ S, |a| ⊓ s = 0 := by
        intro s hs
        have h : |s| ⊓ |a| = 0 := hSJ hs a ha
        rw [abs_of_nonneg (hpos s hs), inf_comm] at h
        exact h
      have h_le : |a| ⊓ y ≤ 0 :=
        key.2 (by rintro _ ⟨s, hs, rfl⟩; exact (hzero s hs).le)
      have h_ge : 0 ≤ |a| ⊓ y := le_inf (abs_nonneg _) hy_nn
      have hay : |a| ⊓ y = 0 := le_antisymm h_le h_ge
      change |y| ⊓ |a| = 0
      rw [abs_of_nonneg hy_nn, inf_comm]; exact hay)
end Band
section Normed
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]
end Normed


