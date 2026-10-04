-- Prove2me | solution 1 for AppliedComb.GraphAlg.cut_lemma
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T17:26:24.042729+00:00
-- url     : https://prove2.me/submissions/22a1df41-2e12-4215-adbb-0bcdd42211e0

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


open SimpleGraph Finset Classical AppliedComb.GraphAlg

namespace GraphAlgProof

theorem exchange_weight_le {V : Type*} [Fintype V] (T : SimpleGraph V)
    (w : Sym2 V → ℕ) {x y : V} (hxy : x ≠ y) (hnot : ¬ T.Adj x y)
    {f : Sym2 V} (hf : f ∈ T.edgeFinset) (hw : w s(x,y) ≤ w f) :
    weight w (exchange T x y f) ≤ weight w T := by
  classical
  have hx : s(x,y) ∉ T.edgeFinset.erase f := by simp [hnot]
  simp only [weight, exchange_edgeFinset T x y f hxy hnot,
    Finset.sum_insert hx]
  have hs := Finset.sum_erase_add _ w hf
  omega

theorem cut_oriented {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected)
    (w : Sym2 V → ℕ) (F : SimpleGraph V) (hF : IsSpanningForest G F)
    (C : F.ConnectedComponent) (x y : V) (hxy : G.Adj x y)
    (hx : x ∈ C.supp) (hy : y ∉ C.supp)
    (hmin : ∀ u v : V, G.Adj u v → u ∈ C.supp → v ∉ C.supp →
      w s(x,y) ≤ w s(u,v)) :
    ∃ T : SimpleGraph V, IsSpanningTree G T ∧ F ≤ T ∧ T.Adj x y ∧
      ∀ T' : SimpleGraph V, IsSpanningTree G T' → F ≤ T' → weight w T ≤ weight w T' := by
  classical
  let A := {T : SimpleGraph V // IsSpanningTree G T ∧ F ≤ T}
  haveI : Nonempty A := by
    obtain ⟨T,hFT,hTG,hT⟩ := hG.exists_isTree_le_of_le_of_isAcyclic hF.1 hF.2
    exact ⟨⟨T,⟨⟨hTG,hT⟩,hFT⟩⟩⟩
  let T : A := Function.argmin (fun T : A => weight w T.val)
  have hopt (U : SimpleGraph V) (hU : IsSpanningTree G U) (hFU : F ≤ U) :
      weight w T.val ≤ weight w U :=
    Function.argmin_le (fun T : A => weight w T.val) (⟨U,hU,hFU⟩ : A)
  by_cases hTxy : T.val.Adj x y
  · exact ⟨T.val,T.property.1,T.property.2,hTxy,hopt⟩
  obtain ⟨p,hp,_⟩ := T.property.1.2.existsUnique_path x y
  obtain ⟨d,hd,hdx,hdy⟩ := p.exists_boundary_dart C.supp hx hy
  have hdf : d.edge ∈ p.edges := List.mem_map.mpr ⟨d,hd,rfl⟩
  have hnF : d.edge ∉ F.edgeSet := by
    intro he
    exact hdy (C.mem_supp_of_adj_mem_supp hdx he)
  let U := exchange T.val x y d.edge
  have hUT : IsSpanningTree G U :=
    ⟨exchange_le T.property.1.1 hxy _,
      exchange_isTree T.property.1.2 hxy.ne hTxy p hp hdf⟩
  have hFU : F ≤ U := by
    intro a b hab
    apply Or.inl
    refine ⟨T.property.2 hab, ?_⟩
    intro heq
    apply hnF
    have heq' : s(a,b) = d.edge := heq.1
    rw [← heq']
    exact hab
  have hUxy : U.Adj x y := Or.inr ((edge_adj x y x y).mpr ⟨Or.inl ⟨rfl,rfl⟩,hxy.ne⟩)
  have hweight : weight w U ≤ weight w T.val :=
    exchange_weight_le T.val w hxy.ne hTxy (by simpa using p.edges_subset_edgeSet hdf)
      (hmin d.fst d.snd (T.property.1.1 d.adj) hdx hdy)
  exact ⟨U,hUT,hFU,hUxy,fun T' hT' hFT' => hweight.trans (hopt T' hT' hFT')⟩

end GraphAlgProof


open SimpleGraph AppliedComb.GraphAlg

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected)
    (w : Sym2 V → ℕ) (F : SimpleGraph V) (hF : IsSpanningForest G F)
    (C : F.ConnectedComponent) (x y : V) (hxy : G.Adj x y)
    (hcross : (x ∈ C.supp ∧ y ∉ C.supp) ∨ (y ∈ C.supp ∧ x ∉ C.supp))
    (hmin : ∀ u v : V, G.Adj u v → u ∈ C.supp → v ∉ C.supp → w s(x, y) ≤ w s(u, v)) :
    ∃ T : SimpleGraph V, IsSpanningTree G T ∧ F ≤ T ∧ T.Adj x y ∧
      ∀ T' : SimpleGraph V, IsSpanningTree G T' → F ≤ T' → weight w T ≤ weight w T' := by
  rcases hcross with ⟨hx,hy⟩ | ⟨hy,hx⟩
  · exact GraphAlgProof.cut_oriented G hG w F hF C x y hxy hx hy hmin
  · obtain ⟨T,hT,hFT,hyx,hopt⟩ := GraphAlgProof.cut_oriented G hG w F hF C y x
      hxy.symm hy hx (by simpa only [Sym2.eq_swap] using hmin)
    exact ⟨T,hT,hFT,hyx.symm,hopt⟩

#print axioms solution
