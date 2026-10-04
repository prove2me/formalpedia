-- Prove2me | solution 1 for AppliedComb.Ramsey.six_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:21:09.6863+00:00
-- url     : https://prove2.me/submissions/fb051ca7-fbbb-4173-9fda-7728c2263cfa

import Mathlib

set_option autoImplicit false

theorem ramsey33_aux_0b0c4dc0 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V)
    (h : 3 ≤ (Finset.univ.filter (fun w => G.Adj v w)).card) :
    (∃ s : Finset V, G.IsNClique 3 s) ∨ (∃ s : Finset V, G.IsNIndepSet 3 s) := by
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq h
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp htc
  have ha : G.Adj v a := by simpa using ht (by simp : a ∈ ({a, b, c} : Finset V))
  have hb : G.Adj v b := by simpa using ht (by simp : b ∈ ({a, b, c} : Finset V))
  have hc : G.Adj v c := by simpa using ht (by simp : c ∈ ({a, b, c} : Finset V))
  by_cases h1 : G.Adj a b
  · exact Or.inl ⟨{v, a, b}, SimpleGraph.is3Clique_triple_iff.mpr ⟨ha, hb, h1⟩⟩
  by_cases h2 : G.Adj a c
  · exact Or.inl ⟨{v, a, c}, SimpleGraph.is3Clique_triple_iff.mpr ⟨ha, hc, h2⟩⟩
  by_cases h3 : G.Adj b c
  · exact Or.inl ⟨{v, b, c}, SimpleGraph.is3Clique_triple_iff.mpr ⟨hb, hc, h3⟩⟩
  refine Or.inr ⟨{a, b, c}, ?_⟩
  rw [← SimpleGraph.isNClique_compl, SimpleGraph.is3Clique_triple_iff]
  simp only [SimpleGraph.compl_adj]
  exact ⟨⟨hab, h1⟩, ⟨hac, h2⟩, ⟨hbc, h3⟩⟩

theorem solution (V : Type) [Fintype V] (hV : 6 ≤ Fintype.card V) (G : SimpleGraph V) :
    (∃ s : Finset V, G.IsNClique 3 s) ∨ (∃ s : Finset V, G.IsNIndepSet 3 s) := by
  classical
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
    (fun w => G.Adj v w)
  have h2 : Finset.univ.filter (fun w => Gᶜ.Adj v w)
      = (Finset.univ.filter (fun w => ¬ G.Adj v w)).erase v := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      SimpleGraph.compl_adj]
    constructor
    · rintro ⟨h, h'⟩; exact ⟨Ne.symm h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨Ne.symm h, h'⟩
  have h3 : v ∈ Finset.univ.filter (fun w => ¬ G.Adj v w) := by simp
  have h4 : (Finset.univ.filter (fun w => Gᶜ.Adj v w)).card
      = (Finset.univ.filter (fun w => ¬ G.Adj v w)).card - 1 := by
    rw [h2, Finset.card_erase_of_mem h3]
  have h5 : 0 < (Finset.univ.filter (fun w => ¬ G.Adj v w)).card :=
    Finset.card_pos.mpr ⟨v, h3⟩
  rw [Finset.card_univ] at h1
  by_cases h : 3 ≤ (Finset.univ.filter (fun w => G.Adj v w)).card
  · exact ramsey33_aux_0b0c4dc0 G v h
  · have h' : 3 ≤ (Finset.univ.filter (fun w => Gᶜ.Adj v w)).card := by omega
    rcases ramsey33_aux_0b0c4dc0 Gᶜ v h' with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact Or.inr ⟨s, by simpa using hs⟩
    · exact Or.inl ⟨s, by simpa using hs⟩
