-- Prove2me | solution 1 for AppliedComb.Ramsey.ramsey_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:23:32.135535+00:00
-- url     : https://prove2.me/submissions/ffff8ed5-9239-4fdd-9060-2d0f3c7e9369

import Mathlib
import Definitions.Def_AppliedComb_Ramsey_ramseyNumber

set_option autoImplicit false

theorem bbe513a4_key {V : Type} (G : SimpleGraph V) (m : ℕ) :
    ∀ (n : ℕ) (S : Finset V), 2 ^ (m + n) ≤ S.card →
      (∃ s ⊆ S, G.IsNClique m s) ∨ (∃ s ⊆ S, Gᶜ.IsNClique n s) := by
  classical
  induction m with
  | zero =>
    intro n S _
    left
    exact ⟨∅, Finset.empty_subset _, by simp⟩
  | succ m ihm =>
    intro n
    induction n with
    | zero =>
      intro S _
      right
      exact ⟨∅, Finset.empty_subset _, by simp⟩
    | succ n ihn =>
      intro S hS
      have hpos : 0 < S.card := lt_of_lt_of_le (pow_pos two_pos _) hS
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      set A := (S.erase v).filter (fun w => G.Adj v w) with hAdef
      set B := (S.erase v).filter (fun w => ¬ G.Adj v w) with hBdef
      have hAB : A.card + B.card = S.card - 1 := by
        rw [hAdef, hBdef, Finset.card_filter_add_card_filter_not,
          Finset.card_erase_of_mem hv]
      have hsplit : 2 ^ (m + (n + 1)) ≤ A.card ∨ 2 ^ ((m + 1) + n) ≤ B.card := by
        by_contra h
        simp only [not_or, not_le] at h
        have e1 : m + (n + 1) = m + n + 1 := by ring
        have e2 : (m + 1) + n = m + n + 1 := by ring
        have e3 : m + 1 + (n + 1) = m + n + 1 + 1 := by ring
        rw [e1] at h
        rw [e2] at h
        rw [e3, pow_succ] at hS
        omega
      have hAS : A ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have hBS : B ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      rcases hsplit with hA | hB
      · rcases ihm (n + 1) A hA with ⟨s, hsA, hs⟩ | ⟨s, hsA, hs⟩
        · left
          refine ⟨insert v s, Finset.insert_subset hv (hsA.trans hAS), ?_⟩
          refine hs.insert ?_
          intro b hb
          have := hsA hb
          rw [hAdef, Finset.mem_filter] at this
          exact this.2
        · right
          exact ⟨s, hsA.trans hAS, hs⟩
      · rcases ihn B hB with ⟨s, hsB, hs⟩ | ⟨s, hsB, hs⟩
        · left
          exact ⟨s, hsB.trans hBS, hs⟩
        · right
          refine ⟨insert v s, Finset.insert_subset hv (hsB.trans hBS), ?_⟩
          refine hs.insert ?_
          intro b hb
          have := hsB hb
          rw [hBdef, Finset.mem_filter, Finset.mem_erase] at this
          rw [SimpleGraph.compl_adj]
          exact ⟨fun h => this.1.1 h.symm, this.2⟩

open AppliedComb.Ramsey in
theorem solution (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsLeast {N : ℕ | 0 < N ∧ IsRamseyBound m n N} (ramseyNumber m n) := by
  have hne : {N : ℕ | 0 < N ∧ IsRamseyBound m n N}.Nonempty := by
    refine ⟨2 ^ (m + n), pow_pos two_pos _, ?_⟩
    intro V _ hV G
    classical
    rcases bbe513a4_key G m n Finset.univ (by simpa using hV) with ⟨s, -, hs⟩ | ⟨s, -, hs⟩
    · exact Or.inl ⟨s, hs⟩
    · exact Or.inr ⟨s, by simpa using hs⟩
  exact ⟨Nat.sInf_mem hne, fun N hN => Nat.sInf_le hN⟩
