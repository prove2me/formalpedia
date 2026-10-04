-- Prove2me | solution 1 for AppliedComb.Ramsey.hypergraph_ramsey
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:19:04.794038+00:00
-- url     : https://prove2.me/submissions/9840f624-0f35-4039-9241-7f43276f9209

import Mathlib
import Definitions.Def_AppliedComb_Ramsey_hypergraphRamseyNumber

namespace HypRamseyAux

/-- The Ramsey property for an arbitrary ground type `ι` and a colouring of all finite sets. -/
def Good (s r : ℕ) (h : Fin r → ℕ) (N : ℕ) : Prop :=
  ∀ (ι : Type) (X : Finset ι) (c : Finset ι → Fin r), N ≤ X.card →
    ∃ α : Fin r, ∃ H ⊆ X, H.card = h α ∧ ∀ S ⊆ H, S.card = s → c S = α

/-- Base case `s = 0`. -/
lemma good_zero {r : ℕ} (h : Fin r → ℕ) : ∃ N, Good 0 r h N := by
  refine ⟨∑ i, h i, ?_⟩
  intro ι X c hX
  refine ⟨c ∅, ?_⟩
  have hle : h (c ∅) ≤ ∑ i, h i :=
    Finset.single_le_sum (f := h) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  obtain ⟨H, hHX, hH⟩ := Finset.exists_subset_card_eq (hle.trans hX)
  refine ⟨H, hHX, hH, fun S _ hS => ?_⟩
  have : S = ∅ := Finset.card_eq_zero.mp hS
  rw [this]

/-- Trivial case: some target size is smaller than the subset size. -/
lemma good_of_small {s r : ℕ} (h : Fin r → ℕ) (i : Fin r) (hi : h i ≤ s) :
    Good (s + 1) r h (h i) := by
  intro ι X c hX
  obtain ⟨H, hHX, hH⟩ := Finset.exists_subset_card_eq hX
  refine ⟨i, H, hHX, hH, fun S hSH hS => ?_⟩
  have := Finset.card_le_card hSH
  omega

/-- Replacing `h i` by `h i - 1` lowers the total by one. -/
lemma sum_update_lt {r : ℕ} (h : Fin r → ℕ) (i : Fin r) (hpos : 0 < h i) :
    ∑ j, Function.update h i (h i - 1) j < ∑ j, h j := by
  have h1 := Finset.sum_update_of_mem (Finset.mem_univ i) h (h i - 1)
  have h2 := Finset.sum_sdiff (Finset.subset_univ ({i} : Finset (Fin r))) (f := h)
  rw [Finset.sum_singleton] at h2
  omega

/-- The inductive step. -/
lemma good_succ {s r : ℕ} (IHs : ∀ h : Fin r → ℕ, ∃ N, Good s r h N) :
    ∀ m : ℕ, ∀ h : Fin r → ℕ, ∑ i, h i = m → ∃ N, Good (s + 1) r h N := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro h hm
  by_cases hsmall : ∃ i, h i ≤ s
  · obtain ⟨i, hi⟩ := hsmall
    exact ⟨h i, good_of_small h i hi⟩
  have hsmall : ∀ i, s < h i := fun i => not_le.mp (not_exists.mp hsmall i)
  have hpos : ∀ i, 0 < h i := fun i => lt_of_le_of_lt (Nat.zero_le s) (hsmall i)
  -- thresholds for the reduced problems
  have hred : ∀ i : Fin r, ∃ N, Good (s + 1) r (Function.update h i (h i - 1)) N := by
    intro i
    exact IH _ (hm ▸ sum_update_lt h i (hpos i)) _ rfl
  choose Ni hNi using hred
  obtain ⟨M, hM⟩ := IHs Ni
  refine ⟨M + 1, ?_⟩
  intro ι X c hX
  classical
  obtain ⟨x, hx⟩ : X.Nonempty := Finset.card_pos.mp (by omega)
  have hY : M ≤ (X.erase x).card := by
    rw [Finset.card_erase_of_mem hx]; omega
  obtain ⟨i, H', hH'Y, hH'card, hH'col⟩ :=
    hM ι (X.erase x) (fun S => c (insert x S)) hY
  have hxH' : x ∉ H' := fun hxH => by simpa using hH'Y hxH
  obtain ⟨j, H'', hH''H', hH''card, hH''col⟩ :=
    hNi i ι H' c (by rw [hH'card])
  have hH''X : H'' ⊆ X := fun y hy => Finset.mem_of_mem_erase (hH'Y (hH''H' hy))
  by_cases hji : j = i
  · subst hji
    have hxH'' : x ∉ H'' := fun hxH => hxH' (hH''H' hxH)
    refine ⟨j, insert x H'', ?_, ?_, ?_⟩
    · exact Finset.insert_subset hx hH''X
    · rw [Finset.card_insert_of_notMem hxH'', hH''card, Function.update_self]
      have := hpos j
      omega
    · intro S hSH hS
      by_cases hxS : x ∈ S
      · have hS' : S.erase x ⊆ H'' := by
          intro y hy
          have hyx : y ≠ x := Finset.ne_of_mem_erase hy
          have := hSH (Finset.mem_of_mem_erase hy)
          rcases Finset.mem_insert.mp this with h' | h'
          · exact absurd h' hyx
          · exact h'
        have hcard : (S.erase x).card = s := by
          rw [Finset.card_erase_of_mem hxS]; omega
        have := hH'col (S.erase x) (hS'.trans hH''H') hcard
        simpa [Finset.insert_erase hxS] using this
      · have hS' : S ⊆ H'' := (Finset.subset_insert_iff_of_notMem hxS).mp hSH
        exact hH''col S hS' hS
  · refine ⟨j, H'', hH''X, ?_, hH''col⟩
    rw [hH''card, Function.update_of_ne hji]

/-- Existence of Ramsey thresholds for every `s`. -/
lemma good_exists (s r : ℕ) : ∀ h : Fin r → ℕ, ∃ N, Good s r h N := by
  induction s with
  | zero => exact fun h => good_zero h
  | succ s IH => exact fun h => good_succ IH _ h rfl

end HypRamseyAux

theorem solution (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (h : Fin r → ℕ)
    (hh : ∀ i, s ≤ h i) :
    IsLeast {N : ℕ | 0 < N ∧ AppliedComb.Ramsey.IsHypergraphRamseyBound s r h N}
      (AppliedComb.Ramsey.hypergraphRamseyNumber s r h) := by
  obtain ⟨N₀, hN₀⟩ := HypRamseyAux.good_exists s r h
  have hmem : max N₀ 1 ∈ {N : ℕ | 0 < N ∧ AppliedComb.Ramsey.IsHypergraphRamseyBound s r h N} := by
    refine ⟨lt_of_lt_of_le Nat.one_pos (le_max_right _ _), ?_⟩
    intro n hn ϕ
    classical
    let c : Finset (Fin n) → Fin r := fun S =>
      if hS : S.card = s then ϕ ⟨S, hS⟩ else ⟨0, hr⟩
    obtain ⟨α, H, -, hHcard, hHcol⟩ :=
      hN₀ (Fin n) Finset.univ c (by simpa using (le_max_left N₀ 1).trans hn)
    refine ⟨α, H, hHcard, fun S hS hSH => ?_⟩
    have := hHcol S hSH hS
    simpa [c, hS] using this
  exact ⟨Nat.sInf_mem ⟨_, hmem⟩, fun N hN => Nat.sInf_le hN⟩
