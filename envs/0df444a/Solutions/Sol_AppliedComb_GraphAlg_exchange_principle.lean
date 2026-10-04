-- Prove2me | solution 1 for AppliedComb.GraphAlg.exchange_principle
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T17:17:33.751971+00:00
-- url     : https://prove2.me/submissions/8496dc2b-8448-416f-a7f2-db29b3a4bdd8

import Definitions.Def_AppliedComb_GraphAlg_SpanningTree

set_option autoImplicit false


open SimpleGraph Finset

namespace GraphAlgProof

theorem forest_count {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hH : H.IsAcyclic) :
    Nat.card H.edgeSet + Nat.card H.ConnectedComponent = Fintype.card V := by
  classical
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  have hc (c : H.ConnectedComponent) :
      (∑ v : c.supp, H.degree v) + 2 = 2 * Fintype.card c.supp := by
    have ht : (H.induce c.supp).IsTree :=
      ⟨c.connected_toSimpleGraph, hH.induce c.supp⟩
    have hd (v : c.supp) : (H.induce c.supp).degree v = H.degree v := by
      apply degree_induce_of_neighborSet_subset
      intro w hw
      exact c.mem_supp_of_adj_mem_supp v.property hw
    have hs := (H.induce c.supp).sum_degrees_eq_twice_card_edges
    simp_rw [hd] at hs
    have he := ht.card_edgeFinset
    omega
  let e : (Σ c : H.ConnectedComponent, c.supp) ≃ V :=
    Equiv.sigmaFiberEquiv H.connectedComponentMk
  have hv : (∑ c : H.ConnectedComponent, Fintype.card c.supp) = Fintype.card V := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr e
  have hd : (∑ c : H.ConnectedComponent, ∑ v : c.supp, H.degree v) = ∑ v, H.degree v := by
    rw [← Fintype.sum_sigma (f := fun v : Σ c : H.ConnectedComponent, c.supp => H.degree v.2)]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun c _ => hc c)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Finset.mul_sum, hd, hv, H.sum_degrees_eq_twice_card_edges] at hs
  simp only [Nat.card_eq_fintype_card, ← edgeFinset_card]
  omega

theorem acyclic_isTree_of_card {V : Type*} [Fintype V] [Nonempty V]
    {H : SimpleGraph V} (hH : H.IsAcyclic)
    (he : Nat.card H.edgeSet + 1 = Fintype.card V) : H.IsTree := by
  have hc := forest_count H hH
  have hcc : Nat.card H.ConnectedComponent = 1 := by omega
  haveI : Subsingleton H.ConnectedComponent := (Nat.card_eq_one_iff_unique.mp hcc).1
  exact ⟨⟨fun u v => ConnectedComponent.exact (Subsingleton.elim _ _)⟩, hH⟩

end GraphAlgProof


open SimpleGraph Finset Classical

namespace GraphAlgProof

def exchange {V : Type*} (T : SimpleGraph V) (x y : V) (f : Sym2 V) : SimpleGraph V :=
  T.deleteEdges {f} ⊔ edge x y

theorem exchange_edgeFinset {V : Type*} [Fintype V] (T : SimpleGraph V)
    (x y : V) (f : Sym2 V) (hxy : x ≠ y) (hnot : ¬ T.Adj x y) :
    (exchange T x y f).edgeFinset = insert s(x,y) (T.edgeFinset.erase f) := by
  classical
  ext e
  rw [mem_edgeFinset]
  refine Sym2.ind (fun u v => ?_) e
  simp only [Finset.mem_insert, Finset.mem_erase, mem_edgeFinset, mem_edgeSet,
    exchange, sup_adj, deleteEdges_adj, Set.mem_singleton_iff, edge_adj, Sym2.eq_iff]
  grind

theorem exchange_isTree {V : Type*} [Fintype V] {T : SimpleGraph V}
    (ht : T.IsTree) {x y : V} (hxy : x ≠ y) (hnot : ¬ T.Adj x y)
    (p : T.Walk x y) (hp : p.IsPath) {f : Sym2 V} (hf : f ∈ p.edges) :
    (exchange T x y f).IsTree := by
  classical
  haveI : Nonempty V := ht.nonempty
  have hnr : ¬ (T.deleteEdges {f}).Reachable x y := by
    intro hr
    obtain ⟨q,hq⟩ := hr.exists_isPath
    have heq : q.mapLe (T.deleteEdges_le {f}) = p :=
      (ht.existsUnique_path x y).unique (hq.mapLe _) hp
    have hmem : f ∈ (q.mapLe (T.deleteEdges_le {f})).edges := heq ▸ hf
    have hmem' : f ∈ q.edges := by simpa using hmem
    have := q.edges_subset_edgeSet hmem'
    simpa [edgeSet_deleteEdges] using this
  have ha : (exchange T x y f).IsAcyclic :=
    (ht.isAcyclic.anti (T.deleteEdges_le {f})).sup_edge_of_not_reachable hnr
  apply acyclic_isTree_of_card ha
  have hf' : f ∈ T.edgeFinset := by simpa using p.edges_subset_edgeSet hf
  have hx : s(x,y) ∉ T.edgeFinset.erase f := by simp [hnot]
  have hc := ht.card_edgeFinset
  have hpos : 0 < T.edgeFinset.card := Finset.card_pos.mpr ⟨f,hf'⟩
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, exchange_edgeFinset T x y f hxy hnot,
    Finset.card_insert_of_notMem hx, Finset.card_erase_of_mem hf']
  omega

theorem exchange_eq_fromEdgeSet {V : Type*} (T : SimpleGraph V)
    (x y : V) (f : Sym2 V) :
    exchange T x y f = fromEdgeSet (insert s(x,y) {g ∈ T.edgeSet | g ≠ f}) := by
  ext u v
  simp only [exchange, sup_adj, deleteEdges_adj, fromEdgeSet_adj, Set.mem_insert_iff,
    Set.mem_setOf_eq, Set.mem_singleton_iff, mem_edgeSet, edge_adj, Sym2.eq_iff]
  have hn : ¬ T.Adj u u := T.irrefl
  grind

theorem exchange_le {V : Type*} {G T : SimpleGraph V} (ht : T ≤ G)
    {x y : V} (hxy : G.Adj x y) (f : Sym2 V) : exchange T x y f ≤ G := by
  exact sup_le ((T.deleteEdges_le {f}).trans ht) ((edge_le_iff G).mpr (Or.inr hxy))

end GraphAlgProof


open SimpleGraph AppliedComb.GraphAlg

theorem solution {V : Type*} [Fintype V] (G T : SimpleGraph V)
    (hT : IsSpanningTree G T) (x y : V) (he : G.Adj x y) (heT : ¬ T.Adj x y) :
    (∃! P : T.Walk x y, P.IsPath) ∧
      ∀ P : T.Walk x y, P.IsPath → ∀ i : ℕ, i < P.length →
        IsSpanningTree G (SimpleGraph.fromEdgeSet
          (insert s(x, y) {g ∈ T.edgeSet | g ≠ s(P.getVert i, P.getVert (i + 1))})) := by
  refine ⟨hT.2.existsUnique_path x y, ?_⟩
  intro p hp i hi
  rw [← GraphAlgProof.exchange_eq_fromEdgeSet]
  refine ⟨GraphAlgProof.exchange_le hT.1 he _, ?_⟩
  apply GraphAlgProof.exchange_isTree hT.2 he.ne heT p hp
  exact (p.mk_mem_edges_iff_exists).mpr ⟨i, hi, rfl⟩

#print axioms solution
