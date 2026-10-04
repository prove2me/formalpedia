-- Prove2me | solution 1 for AppliedComb.GraphAlg.spanning_forest_edges
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T17:11:10.243744+00:00
-- url     : https://prove2.me/submissions/9b1a6031-3c29-4848-86e6-2d2fbc59a2ef

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


open SimpleGraph Finset

open AppliedComb.GraphAlg

theorem solution {V : Type*} [Fintype V] (G H : SimpleGraph V) (n : ℕ)
    (hn : Fintype.card V = n) (hpos : 0 < n) (hH : IsSpanningForest G H) :
    Nat.card H.edgeSet ≤ n - 1 ∧
      (∀ k : ℕ, Nat.card H.edgeSet + k = n → Nat.card H.ConnectedComponent = k) ∧
      (IsSpanningTree G H ↔ Nat.card H.edgeSet = n - 1) := by
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hc := GraphAlgProof.forest_count H hH.2
  have hp : 0 < Nat.card H.ConnectedComponent := Nat.card_pos
  refine ⟨by omega, fun k hk => by omega, ?_⟩
  constructor
  · intro ht
    have ht' := ht.2.card_edgeFinset
    simpa only [Nat.card_eq_fintype_card, ← edgeFinset_card] using (show
      Fintype.card H.edgeSet = n - 1 from by rw [← edgeFinset_card]; omega)
  · intro he
    have hcc : Nat.card H.ConnectedComponent = 1 := by omega
    haveI : Subsingleton H.ConnectedComponent := (Nat.card_eq_one_iff_unique.mp hcc).1
    refine ⟨hH.1, ⟨?_, hH.2⟩⟩
    exact ⟨fun u v => ConnectedComponent.exact (Subsingleton.elim _ _)⟩

#print axioms solution
