-- Prove2me | solution 1 for AppliedComb.Flows.hall
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:59:07.227597+00:00
-- url     : https://prove2.me/submissions/d831b686-a718-4146-a5e5-a791f0c36fa9

import Mathlib
import Definitions.Def_AppliedComb_Flows_Matching

set_option autoImplicit false

open AppliedComb.Flows in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (V₁ V₂ : Finset V)
    (hbip : IsBipartition G V₁ V₂) :
    (∃ M : Set (Sym2 V), IsMatching G M ∧ ∀ v ∈ V₁, Saturates M v) ↔
      ∀ A : Finset V, A ⊆ V₁ → A.card ≤ (neighborsOf G A).card := by
  classical
  constructor
  · rintro ⟨M, ⟨hMG, hMd⟩, hsat⟩ A hA
    have key : ∀ v ∈ V₁, ∃ w, G.Adj v w ∧ s(v, w) ∈ M := by
      intro v hv
      obtain ⟨e, he, hve⟩ := hsat v hv
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
      exact ⟨w, (SimpleGraph.mem_edgeSet G).mp (hMG he), he⟩
    choose f hfadj hfM using key
    let g : V → V := fun v => if h : v ∈ V₁ then f v h else v
    have hg : ∀ v (h : v ∈ V₁), g v = f v h := fun v h => by simp [g, h]
    apply Finset.card_le_card_of_injOn g
    · intro a ha
      have haV : a ∈ V₁ := hA ha
      simp only [neighborsOf, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      exact ⟨a, ha, by rw [hg a haV]; exact hfadj a haV⟩
    · intro a ha b hb hab
      have haV : a ∈ V₁ := hA ha
      have hbV : b ∈ V₁ := hA hb
      rw [hg a haV, hg b hbV] at hab
      by_cases hed : s(a, f a haV) = s(b, f b hbV)
      · rcases Sym2.eq_iff.mp hed with ⟨h1, _⟩ | ⟨h1, h2⟩
        · exact h1
        · exact absurd (h1.trans hab.symm) ((hfadj a haV).ne)
      · exact ((hMd _ (hfM a haV) _ (hfM b hbV) hed (f b hbV)
          (by rw [← hab]; exact Sym2.mem_mk_right _ _)) (Sym2.mem_mk_right _ _)).elim
  · intro hH
    let t : V₁ → Finset V := fun i => Finset.univ.filter (G.Adj i)
    have hall : ∀ s : Finset V₁, s.card ≤ (s.biUnion t).card := by
      intro s
      have h1 := hH (s.map (Function.Embedding.subtype _)) (by
        intro x hx
        simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
        obtain ⟨y, _, rfl⟩ := hx
        exact y.2)
      rw [Finset.card_map] at h1
      refine h1.trans (Finset.card_le_card ?_)
      intro y hy
      simp only [neighborsOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coe_subtype] at hy
      obtain ⟨x, ⟨x', hx', rfl⟩, hxy⟩ := hy
      simp only [Finset.mem_biUnion, t, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x', hx', hxy⟩
    obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
    have hadj : ∀ i : V₁, G.Adj i (f i) := fun i => by
      have := hf i
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hV2 : ∀ i : V₁, f i ∈ V₂ := fun i => by
      rcases hbip.2.2 _ _ (hadj i) with h | h
      · exact h.2
      · exact absurd i.2 (Finset.disjoint_right.mp hbip.1 h.1)
    have hdis : ∀ x, x ∈ V₁ → x ∈ V₂ → False := fun x h1 h2 =>
      Finset.disjoint_left.mp hbip.1 h1 h2
    refine ⟨Set.range (fun i : V₁ => s((i : V), f i)), ⟨?_, ?_⟩, ?_⟩
    · rintro e ⟨i, rfl⟩
      exact (SimpleGraph.mem_edgeSet G).mpr (hadj i)
    · rintro e ⟨i, rfl⟩ e' ⟨j, rfl⟩ hne v hv hv'
      rw [Sym2.mem_iff] at hv hv'
      rcases hv with rfl | rfl <;> rcases hv' with h | h
      · exact hne (by rw [Subtype.ext h])
      · exact hdis _ i.2 (h ▸ hV2 j)
      · exact hdis _ (h ▸ j.2) (hV2 i)
      · exact hne (by rw [hfinj h])
    · intro v hv
      exact ⟨_, ⟨⟨v, hv⟩, rfl⟩, Sym2.mem_mk_left _ _⟩
