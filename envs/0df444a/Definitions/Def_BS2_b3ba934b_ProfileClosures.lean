-- Prove2me | Definitions.Def_BS2_b3ba934b_ProfileClosures
-- name    : BS2_b3ba934b_ProfileClosures
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T03:35:58.972147+00:00
-- url     : https://prove2.me/theorems/af9bb9ac-0730-43b1-9dda-e086aed274fa
-- title:
--   Sensitivity separation: ProfileClosures (complete source module)
-- statement:
--   Complete Lean source module `ProfileClosures` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ProfileClosures.lean; original SHA-256 351baf21cf080a3b627e16bfefb7da6dbb6f5cd892ef11e4b13bfdca1a2d3417; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Dimension-independent semantics and closure rules for the five sensitivity
profiles. These prove the local soundness of the closure operations, not the
raw graded/min-max transfer formulas or their finite case-table coverage.
-/
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Union
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ThreeBoundProfiles
open OAI.Paper320
noncomputable section
open scoped Classical

variable {L I : Type} [Preorder L] [Fintype I]

def Nested (F : L → (I → Bool) → Bool) : Prop :=
  ∀ i j, i ≤ j → ∀ x, F j x = true → F i x = true

noncomputable def flipsTo (f : (I → Bool) → Bool) (b : Bool) (x : I → Bool) : Finset I := by
  classical
  exact Finset.univ.filter fun a => f (flip x {a}) = b

def ABound (F : L → (I → Bool) → Bool) (i j : L) (v : ℕ) : Prop :=
  ∀ x, F i x = false → (flipsTo (F j) true x).card ≤ v

def BBound (F : L → (I → Bool) → Bool) (i j : L) (v : ℕ) : Prop :=
  ∀ x, F j x = true → (flipsTo (F i) false x).card ≤ v

def MBound (F : L → (I → Bool) → Bool) (i j k : L) (v : ℕ) : Prop :=
  ∀ x, F j x = true → F k x = false → (flipsTo (F i) false x).card ≤ v

def PBound (F : L → (I → Bool) → Bool) (i j k : L) (v : ℕ) : Prop :=
  ∀ x, F i x = true → F j x = false → (flipsTo (F k) true x).card ≤ v

def DBound (F : L → (I → Bool) → Bool) (i j k l : L) (v : ℕ) : Prop :=
  ∀ x, F j x = true → F k x = false →
    ((flipsTo (F i) false x) ∪ (flipsTo (F l) true x)).card ≤ v

theorem rejects_of_le (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤ j) (x : I → Bool) (hi : F i x = false) : F j x = false := by
  cases hj : F j x with
  | false => rfl
  | true => have hh := hF i j hij x hj; rw [hi] at hh; contradiction

theorem up_subset (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤ j) (x : I → Bool) :
    flipsTo (F j) true x ⊆ flipsTo (F i) true x := by
  classical
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF i j hij _ (Finset.mem_filter.mp ha).2⟩

theorem down_subset (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j : L) (hij : i ≤ j) (x : I → Bool) :
    flipsTo (F i) false x ⊆ flipsTo (F j) false x := by
  classical
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    rejects_of_le F hF i j hij _ (Finset.mem_filter.mp ha).2⟩

theorem a_condition_weaken (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i i' j : L) (hii' : i ≤ i') (v : ℕ) (h : ABound F i' j v) : ABound F i j v :=
  fun x hx => h x (rejects_of_le F hF i i' hii' x hx)

theorem a_target_strengthen (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j j' : L) (hjj' : j ≤ j') (v : ℕ) (h : ABound F i j v) : ABound F i j' v :=
  fun x hx => (Finset.card_le_card (up_subset F hF j j' hjj' x)).trans (h x hx)

theorem b_target_weaken (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i i' j : L) (hii' : i ≤ i') (v : ℕ) (h : BBound F i' j v) : BBound F i j v :=
  fun x hx => (Finset.card_le_card (down_subset F hF i i' hii' x)).trans (h x hx)

theorem b_condition_strengthen (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j j' : L) (hjj' : j ≤ j') (v : ℕ) (h : BBound F i j v) : BBound F i j' v :=
  fun x hx => h x (hF j j' hjj' x hx)

theorem m_of_b (F : L → (I → Bool) → Bool) (i j k : L) (v : ℕ)
    (h : BBound F i j v) : MBound F i j k v := fun x hx _ => h x hx

theorem p_of_a (F : L → (I → Bool) → Bool) (i j k : L) (v : ℕ)
    (h : ABound F j k v) : PBound F i j k v := fun x _ hx => h x hx

theorem m_target_weaken (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i i' j k : L) (hii' : i ≤ i') (v : ℕ)
    (h : MBound F i' j k v) : MBound F i j k v :=
  fun x hx hy => (Finset.card_le_card (down_subset F hF i i' hii' x)).trans (h x hx hy)

theorem p_target_strengthen (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j k k' : L) (hkk' : k ≤ k') (v : ℕ)
    (h : PBound F i j k v) : PBound F i j k' v :=
  fun x hx hy => (Finset.card_le_card (up_subset F hF k k' hkk' x)).trans (h x hx hy)

theorem d_of_m_add_p (F : L → (I → Bool) → Bool) (i j k l : L) (m p : ℕ)
    (hm : MBound F i j k m) (hp : PBound F j k l p) : DBound F i j k l (m+p) := by
  intro x hx hy
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hm x hx hy) (hp x hx hy))

theorem d_down_target_weaken (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i i' j k l : L) (hii' : i ≤ i') (v : ℕ)
    (h : DBound F i' j k l v) : DBound F i j k l v := by
  intro x hx hy
  apply (Finset.card_le_card (Finset.union_subset_union (down_subset F hF i i' hii' x)
    (Finset.Subset.refl _))).trans
  exact h x hx hy

theorem d_up_target_strengthen (F : L → (I → Bool) → Bool) (hF : Nested F)
    (i j k l l' : L) (hll' : l ≤ l') (v : ℕ)
    (h : DBound F i j k l v) : DBound F i j k l' v := by
  intro x hx hy
  apply (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl _)
    (up_subset F hF l l' hll' x))).trans
  exact h x hx hy

/-- Split the true condition into the next true state and the intervening gap. -/
theorem b_partition (F : L → (I → Bool) → Bool) (i j k : L) (b m : ℕ)
    (hb : BBound F i k b) (hm : MBound F i j k m) : BBound F i j (max b m) := by
  intro x hx
  cases hk : F k x with
  | false => exact (hm x hx hk).trans (le_max_right _ _)
  | true => exact (hb x hk).trans (le_max_left _ _)

/-- Split a false condition into the preceding false state and the intervening gap. -/
theorem a_partition (F : L → (I → Bool) → Bool) (i j k : L) (a p : ℕ)
    (ha : ABound F i k a) (hp : PBound F i j k p) : ABound F j k (max a p) := by
  intro x hx
  cases hi : F i x with
  | false => exact (ha x hi).trans (le_max_left _ _)
  | true => exact (hp x hi hx).trans (le_max_right _ _)

theorem a_min (F : L → (I → Bool) → Bool) (i j : L) (a b : ℕ)
    (ha : ABound F i j a) (hb : ABound F i j b) : ABound F i j (min a b) :=
  fun x hx => le_min (ha x hx) (hb x hx)

theorem b_min (F : L → (I → Bool) → Bool) (i j : L) (a b : ℕ)
    (ha : BBound F i j a) (hb : BBound F i j b) : BBound F i j (min a b) :=
  fun x hx => le_min (ha x hx) (hb x hx)

theorem m_min (F : L → (I → Bool) → Bool) (i j k : L) (a b : ℕ)
    (ha : MBound F i j k a) (hb : MBound F i j k b) : MBound F i j k (min a b) :=
  fun x hx hy => le_min (ha x hx hy) (hb x hx hy)

theorem p_min (F : L → (I → Bool) → Bool) (i j k : L) (a b : ℕ)
    (ha : PBound F i j k a) (hb : PBound F i j k b) : PBound F i j k (min a b) :=
  fun x hx hy => le_min (ha x hx hy) (hb x hx hy)

theorem d_min (F : L → (I → Bool) → Bool) (i j k l : L) (a b : ℕ)
    (ha : DBound F i j k l a) (hb : DBound F i j k l b) : DBound F i j k l (min a b) :=
  fun x hx hy => le_min (ha x hx hy) (hb x hx hy)

theorem empty_gap_m (F : L → (I → Bool) → Bool) (i j k : L) (heq : F j = F k) :
    MBound F i j k 0 := by
  intro x hj hk
  rw [heq, hk] at hj
  contradiction

theorem empty_gap_p (F : L → (I → Bool) → Bool) (i j k : L) (heq : F i = F j) :
    PBound F i j k 0 := by
  intro x hi hj
  rw [heq, hj] at hi
  contradiction

theorem empty_gap_d (F : L → (I → Bool) → Bool) (i j k l : L) (heq : F j = F k) :
    DBound F i j k l 0 := by
  intro x hj hk
  rw [heq, hk] at hj
  contradiction

/-- The two diagonal profile bounds bound global sensitivity. -/
theorem sensitivity_le_diagonal_max (F : L → (I → Bool) → Bool) (i : L) (a b : ℕ)
    (ha : ABound F i i a) (hb : BBound F i i b) : sensitivity (F i) ≤ max a b := by
  classical
  apply Finset.sup_le
  intro x _
  cases hx : F i x with
  | false =>
      have he : sensitivityAt (F i) x = (flipsTo (F i) true x).card := by
        simp [sensitivityAt, flipsTo, hx]
      rw [he]
      exact (ha x hx).trans (le_max_left _ _)
  | true =>
      have he : sensitivityAt (F i) x = (flipsTo (F i) false x).card := by
        simp [sensitivityAt, flipsTo, hx]
      rw [he]
      exact (hb x hx).trans (le_max_right _ _)

end
end ThreeBoundProfiles

#print axioms ThreeBoundProfiles.a_partition
#print axioms ThreeBoundProfiles.b_partition
#print axioms ThreeBoundProfiles.d_of_m_add_p
#print axioms ThreeBoundProfiles.sensitivity_le_diagonal_max


