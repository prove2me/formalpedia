-- Prove2me | solution 1 for AppliedComb.Graphs.interval_chromatic_eq_clique
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:45:38.472378+00:00
-- url     : https://prove2.me/submissions/efd4f0bb-b907-4383-a219-8f07915244f8

import Mathlib
import Definitions.Def_AppliedComb_Graphs_IsIntervalGraph

open Finset

namespace IntervalAux

/-- Greedy colouring along the left endpoints: every finset of vertices of an interval graph
carries a proper colouring with colours below the clique number. -/
lemma greedy_colouring {V : Type*} [Fintype V] (G : SimpleGraph V) (a b : V → ℝ)
    (hab : ∀ v, a v ≤ b v)
    (hadj : ∀ u v : V, u ≠ v → (G.Adj u v ↔ (Set.Icc (a u) (b u) ∩ Set.Icc (a v) (b v)).Nonempty))
    (S : Finset V) :
    ∃ c : V → ℕ, (∀ v ∈ S, c v < G.cliqueNum) ∧
      ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v := by
  classical
  induction S using Finset.induction_on_max_value a with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | insert x s hxs hmax ih =>
    obtain ⟨c, hc, hproper⟩ := ih
    -- the earlier neighbours of `x`
    set N : Finset V := s.filter (fun y => G.Adj x y) with hN
    have hclique : G.IsClique (↑(insert x N) : Set V) := by
      intro u hu v hv huv
      rw [Finset.mem_coe, Finset.mem_insert] at hu hv
      have hpt : ∀ y ∈ N, a x ∈ Set.Icc (a y) (b y) := by
        intro y hy
        rw [hN, Finset.mem_filter] at hy
        have hxy : x ≠ y := fun h => hxs (h ▸ hy.1)
        obtain ⟨z, hz1, hz2⟩ := (hadj x y hxy).1 hy.2
        exact ⟨hmax y hy.1, by linarith [hz1.1, hz2.2, hz2.1, hz1.2]⟩
      have hself : a x ∈ Set.Icc (a x) (b x) := ⟨le_rfl, hab x⟩
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact absurd rfl huv
      · exact (Finset.mem_filter.1 hv).2
      · exact ((Finset.mem_filter.1 hu).2).symm
      · exact (hadj u v huv).2 ⟨a x, hpt u hu, hpt v hv⟩
    have hxN : x ∉ N := fun h => hxs (Finset.mem_filter.1 h).1
    have hcard : N.card + 1 ≤ G.cliqueNum := by
      have := SimpleGraph.IsClique.card_le_cliqueNum (G := G) (t := insert x N) (tc := hclique)
      rwa [Finset.card_insert_of_notMem hxN] at this
    -- a free colour
    have hfree : ∃ k, k < G.cliqueNum ∧ k ∉ N.image c := by
      by_contra hno
      push Not at hno
      have hsub : Finset.range G.cliqueNum ⊆ N.image c := fun k hk =>
        hno k (Finset.mem_range.1 hk)
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_range] at h1
      have h2 := Finset.card_image_le (s := N) (f := c)
      omega
    obtain ⟨k, hk, hkN⟩ := hfree
    refine ⟨Function.update c x k, ?_, ?_⟩
    · intro v hv
      rw [Finset.mem_insert] at hv
      rcases hv with rfl | hv
      · simpa using hk
      · have hvx : v ≠ x := fun h => hxs (h ▸ hv)
        rw [Function.update_of_ne hvx]
        exact hc v hv
    · intro u hu v hv huv
      rw [Finset.mem_insert] at hu hv
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact absurd huv (G.loopless.irrefl _)
      · have hvx : v ≠ u := fun h => hxs (h ▸ hv)
        rw [Function.update_self, Function.update_of_ne hvx]
        intro h
        apply hkN
        rw [Finset.mem_image]
        exact ⟨v, Finset.mem_filter.2 ⟨hv, huv⟩, by rw [h]⟩
      · have hux : u ≠ v := fun h => hxs (h ▸ hu)
        rw [Function.update_self, Function.update_of_ne hux]
        intro h
        apply hkN
        rw [Finset.mem_image]
        exact ⟨u, Finset.mem_filter.2 ⟨hu, huv.symm⟩, by rw [← h]⟩
      · have hux : u ≠ x := fun h => hxs (h ▸ hu)
        have hvx : v ≠ x := fun h => hxs (h ▸ hv)
        rw [Function.update_of_ne hux, Function.update_of_ne hvx]
        exact hproper u hu v hv huv

end IntervalAux

/-- Interval graphs satisfy `χ = ω`. -/
theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : AppliedComb.Graphs.IsIntervalGraph G) : G.chromaticNumber = (G.cliqueNum : ℕ∞) := by
  obtain ⟨a, b, hab, hadj⟩ := hG
  obtain ⟨c, hc, hproper⟩ := IntervalAux.greedy_colouring G a b hab hadj Finset.univ
  have hcol : G.Colorable G.cliqueNum :=
    ⟨SimpleGraph.Coloring.mk (fun v => (⟨c v, hc v (Finset.mem_univ v)⟩ : Fin G.cliqueNum))
      (fun {u v} h => by
        intro heq
        exact hproper u (Finset.mem_univ u) v (Finset.mem_univ v) h (congrArg Fin.val heq))⟩
  exact le_antisymm hcol.chromaticNumber_le G.cliqueNum_le_chromaticNumber
