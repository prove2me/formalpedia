-- Prove2me | Definitions.Def_LeanPool_CriticalPortraits_Portraits
-- name    : LeanPool_CriticalPortraits_Portraits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:24:12.97759+00:00
-- url     : https://prove2.me/theorems/dca98f12-244a-4ccf-919c-e2bbde6b07b3
-- title:
--   Portraits
-- statement:
--   Definitions and structural lemmas for Portraits, from Keston Aquino-Michaels; LeanPool contributors's pinned Counting critical portraits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean

module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CriticalPortraits
open Finset
open scoped BigOperators
def IsCriticalSet (d m : ℕ) (S : Finset (ZMod (d * m))) : Prop :=
  (∃ r, r < m ∧ ∀ x ∈ S, x.val % m = r) ∧ 2 ≤ S.card
instance (d m : ℕ) (S : Finset (ZMod (d * m))) : Decidable (IsCriticalSet d m S) := by
  unfold IsCriticalSet; infer_instance
def Linked {N : ℕ} (A B : Finset (ZMod N)) : Prop :=
  ∃ a1 ∈ A, ∃ a2 ∈ A, ∃ b1 ∈ B, ∃ b2 ∈ B,
    (a1.val < b1.val ∧ b1.val < a2.val ∧ a2.val < b2.val) ∨
    (b1.val < a1.val ∧ a1.val < b2.val ∧ b2.val < a2.val)
instance {N : ℕ} (A B : Finset (ZMod N)) : Decidable (Linked A B) := by
  unfold Linked; infer_instance
def Unlinked {N : ℕ} (A B : Finset (ZMod N)) : Prop := ¬ Linked A B
instance {N : ℕ} (A B : Finset (ZMod N)) : Decidable (Unlinked A B) := by
  unfold Unlinked; infer_instance
theorem Unlinked.symm {N : ℕ} {A B : Finset (ZMod N)} (h : Unlinked A B) : Unlinked B A := by
  intro hL
  apply h
  obtain ⟨b1, hb1, b2, hb2, a1, ha1, a2, ha2, hcase⟩ := hL
  rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨a1, ha1, a2, ha2, b1, hb1, b2, hb2, Or.inr ⟨h1, h2, h3⟩⟩
  · exact ⟨a1, ha1, a2, ha2, b1, hb1, b2, hb2, Or.inl ⟨h1, h2, h3⟩⟩
def Portrait (d m : ℕ) (P : Finset (Finset (ZMod (d * m)))) : Prop :=
  (∀ S ∈ P, IsCriticalSet d m S) ∧
  (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
  (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Unlinked A B) ∧
  (∑ S ∈ P, (S.card - 1) = d - 1)
instance (d m : ℕ) (P : Finset (Finset (ZMod (d * m)))) : Decidable (Portrait d m P) := by
  unfold Portrait; infer_instance
lemma portrait_eq_empty_of_degenerate (d m : ℕ) (h0 : d * m = 0)
    (P : Finset (Finset (ZMod (d * m)))) (hP : Portrait d m P) : P = ∅ := by
  classical
  obtain ⟨hcrit, _, _, hw⟩ := hP
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0: no fiber witness possible (r < 0 is impossible), so P has no element
    by_contra hne
    obtain ⟨S, hS⟩ := Finset.nonempty_of_ne_empty hne
    obtain ⟨⟨r, hr, _⟩, _⟩ := hcrit S hS
    omega
  · -- m > 0 ⇒ d = 0; weight target d - 1 = 0, but each S has card ≥ 2 ⇒ weight ≥ 1
    have hd0 : d = 0 := by
      rcases Nat.eq_zero_or_pos d with h | h
      · exact h
      · exfalso; have : 0 < d * m := Nat.mul_pos h hmpos; omega
    by_contra hne
    obtain ⟨S, hS⟩ := Finset.nonempty_of_ne_empty hne
    have hcardS : 2 ≤ S.card := (hcrit S hS).2
    have hpos : 0 < ∑ T ∈ P, (T.card - 1) := by
      apply Finset.sum_pos'
      · intro i _; exact Nat.zero_le _
      · exact ⟨S, hS, by omega⟩
    simp_all
instance instFinitePortrait (d m : ℕ) :
    Finite {P : Finset (Finset (ZMod (d * m))) // Portrait d m P} := by
  rcases Nat.eq_zero_or_pos (d * m) with h0 | hpos
  · exact Finite.of_injective (fun _ => (0 : Unit)) (by
      intro a b _
      exact Subtype.ext ((portrait_eq_empty_of_degenerate d m h0 a.1 a.2).trans
        (portrait_eq_empty_of_degenerate d m h0 b.1 b.2).symm))
  · have : NeZero (d * m) := ⟨hpos.ne'⟩
    infer_instance
noncomputable instance instFintypePortrait (d m : ℕ) :
    Fintype {P : Finset (Finset (ZMod (d * m))) // Portrait d m P} :=
  Fintype.ofFinite _
noncomputable def minVal {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) : ZMod N :=
  (Finset.exists_min_image S (fun x => x.val) h).choose
lemma minVal_mem {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) : minVal S h ∈ S :=
  (Finset.exists_min_image S (fun x => x.val) h).choose_spec.1
noncomputable def eraseMin {N : ℕ} (S : Finset (ZMod N)) : Finset (ZMod N) :=
  if h : S.Nonempty then S.erase (minVal S h) else S
lemma eraseMin_subset {N : ℕ} (S : Finset (ZMod N)) : eraseMin S ⊆ S := by
  unfold eraseMin
  split
  · exact Finset.erase_subset _ _
  · exact subset_rfl
lemma eraseMin_card {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) :
    (eraseMin S).card = S.card - 1 := by
  unfold eraseMin
  rw [dif_pos h, Finset.card_erase_of_mem (minVal_mem S h)]
noncomputable def T {N : ℕ} (P : Finset (Finset (ZMod N))) : Finset (ZMod N) :=
  P.sup eraseMin
lemma eraseMin_pairwiseDisjoint {d m : ℕ} (P : Finset (Finset (ZMod (d * m))))
    (hP : Portrait d m P) : (↑P : Set (Finset (ZMod (d * m)))).PairwiseDisjoint eraseMin := by
  intro A hA B hB hAB
  exact (hP.2.1 A hA B hB hAB).mono (eraseMin_subset A) (eraseMin_subset B)
theorem T_card {d m : ℕ} {P : Finset (Finset (ZMod (d * m)))}
    (hP : Portrait d m P) : (T P).card = d - 1 := by
  classical
  unfold T
  rw [Finset.sup_eq_biUnion, Finset.card_biUnion (eraseMin_pairwiseDisjoint P hP)]
  rw [← hP.2.2.2]
  apply Finset.sum_congr rfl
  intro S hS
  have hcard : 2 ≤ S.card := (hP.1 S hS).2
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  exact eraseMin_card S hne
noncomputable def TsubCard {d m : ℕ} {P : Finset (Finset (ZMod (d * m)))}
    (hP : Portrait d m P) : {S : Finset (ZMod (d * m)) // S.card = d - 1} :=
  ⟨T P, T_card hP⟩
end CriticalPortraits


