-- Prove2me | Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Shrink
-- name    : LeanPool_NashWilliams_Combinatorics_Front_Shrink
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:43:21.910013+00:00
-- url     : https://prove2.me/theorems/e9fc5c3d-7e2d-4265-b2f4-e00897f9d8ad
-- title:
--   Shrink
-- statement:
--   Definitions and structural lemmas for Shrink, from Yann Pequignot; LeanPool contributors's pinned Nash-Williams fronts and better-quasi-orders development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Shrink.lean

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Theorems.Thm_Front_IsInit_head_eq
public import Theorems.Thm_Front_isInit_nil
public import Theorems.Thm_List_IsPrefix_head_eq
attribute [local simp] Front.isInit_nil


set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set List
noncomputable section
namespace Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
def shrink (F : Set (List ℕ)) (N : ℕ → ℕ) : Set (List ℕ) :=
  {s | s ∈ F ∧ ∀ x ∈ s, x ∈ Set.range N}
def shrinkOn (F : Set (List ℕ)) (X : Set ℕ) : Set (List ℕ) :=
  {s | s ∈ F ∧ ∀ x ∈ s, x ∈ X}
theorem shrink_isFront (hF : IsFront F M) {E : ℕ → ℕ} (hE : StrictMono E) :
    IsFront (shrink F (M ∘ E)) (M ∘ E) where
  mono := hF.mono.comp hE
  sorted s hs := hF.sorted s hs.1
  subM s hs := hs.2
  incomp s hs t ht hst := hF.incomp s hs.1 t ht.1 hst
  dense g hg := by
    obtain ⟨u, hu, hInit⟩ := hF.dense (E ∘ g) (hE.comp hg)
    refine ⟨u, ⟨hu, ?_⟩, hInit⟩
    intro x hx
    rw [hInit, List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact ⟨g i, rfl⟩
  base := by
    by_cases h0 : [] ∈ F
    · -- `F = {[]}`, so `shrink F N = {[]}`
      left
      ext s
      simp only [shrink, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hsF, -⟩
        exact (hF.incomp [] h0 s hsF List.nil_prefix).symm
      · rintro rfl
        exact ⟨h0, by simp⟩
    · -- nontrivial: the elements of `shrink F N` cover `N`
      right
      ext x
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨s, hs, hxs⟩
        exact hs.2 x hxs
      · rintro ⟨k, rfl⟩
        have hg : StrictMono (fun x => k + x) := add_right_strictMono
        obtain ⟨u, hu, hInit⟩ := hF.dense (E ∘ (fun x => k + x)) (hE.comp hg)
        have hune : u ≠ [] := fun h => h0 (h ▸ hu)
        have huN : ∀ y ∈ u, y ∈ Set.range (M ∘ E) := by
          intro y hy
          rw [hInit, List.mem_map] at hy
          obtain ⟨i, _, rfl⟩ := hy
          exact ⟨k + i, rfl⟩
        refine ⟨u, ⟨hu, huN⟩, ?_⟩
        have hhead : u.head? = some ((M ∘ E) k) := by rw [hInit.head_eq hune]; simp
        obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hhead
        rw [hys]; simp
end Front


