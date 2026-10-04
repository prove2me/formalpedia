-- Prove2me | solution 1 for AppliedComb.Graphs.tree_two_leaves
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:47:40.585393+00:00
-- url     : https://prove2.me/submissions/2f644300-4487-44a7-b7e3-1f9477425c1d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_AppliedComb_Graphs_IsCycle

/-
Keller--Trotter, Applied Combinatorics (2017), Proposition 5.11.
The mathematical two-leaves result is supplied by Mathlib. The bridge below
checks that the platform's list-based notion of a tree satisfies its hypotheses.
-/

private theorem platform_tree_isTree {V : Type*} (G : SimpleGraph V)
    (hT : AppliedComb.Graphs.IsTree G) : G.IsTree := by
  refine (SimpleGraph.isTree_iff G).2 ⟨hT.1, ?_⟩
  intro v p hp
  apply hT.2
  refine ⟨p.tail.support, ?_, hp.isPath_tail.support_nodup,
    p.tail.isChain_adj_support, p.snd, v, ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.length_support,
      SimpleGraph.Walk.length_tail_add_one hp.not_nil]
    exact hp.three_le_length
  · rw [List.head?_eq_some_head p.tail.support_ne_nil]
    simp
  · rw [List.getLast?_eq_some_getLast p.tail.support_ne_nil]
    simp
  · exact (p.adj_snd hp.not_nil).symm

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n) (h2 : 2 ≤ n)
    (hT : AppliedComb.Graphs.IsTree G) :
    2 ≤ (Finset.univ.filter (fun v : V => G.degree v = 1)).card := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, v, huv, hu, hv⟩ :=
    (platform_tree_isTree G hT).exists_ne_and_degree_eq_one
  exact Finset.one_lt_card.mpr
    ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩,
      v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩, huv⟩
