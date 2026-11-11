-- Prove2me | Definitions.Def_STCSublinear1377_Main_Expansion
-- name    : STCSublinear1377_Main_Expansion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:42.351481+00:00
-- url     : https://prove2.me/theorems/6d588f55-b2d9-466c-9f45-3fe59e0ec3f8
-- title:
--   Simultaneous tree substitution with selected original endpoints
-- statement:
--   Let $Q$ and $Q'$ be quotients of a common weighted graph, with the second partition refining the first. For each expanded coarse bag $A$, choose a spanning tree $T_A$ of the induced refined quotient. Retain a selected original edge for every edge of an old spanning tree $T$ of $Q$. Substitute all the local trees and attach each old incident edge to the fine cell containing its selected endpoint:
--
--   $$T'=T[\,A\leftarrow T_A\,].$$
--
--   The data record the parent map between bags, their exact unions, the unchanged bags, the input trees, and the selected endpoints. The result has an explicit adjacency formula, covering simultaneous expansions of disjoint bags. These are structural inputs only: neither spanning-tree correctness of the result nor a load inequality is assumed.
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Lemma 3.3, PDF/printed pp.9–10, equations (3.2)–(3.3)

import Definitions.Def_STCSublinear1377_Main_Quotient
set_option autoImplicit false

namespace STCSublinear1377.Main

/-- Input data for simultaneous refinement of disjoint bags. Only partition/refinement data
and the input trees are recorded; none of the resulting load bounds are fields. -/
structure Expansion {n : ℕ} (f : WeightedGraph n) where
  coarse : BagPartition f
  fine : BagPartition f
  parent : Fin n → Fin n
  parent_mem : ∀ b ∈ fine.names, parent b ∈ coarse.names
  refined : Finset (Fin n)
  refined_mem : refined ⊆ coarse.names
  unions : ∀ a ∈ coarse.names,
    (fine.names.filter (fun b => parent b = a)).biUnion fine.bag = coarse.bag a
  unchanged : ∀ a ∈ coarse.names, a ∉ refined →
    a ∈ fine.names ∧ parent a = a ∧ fine.bag a = coarse.bag a ∧
      (∀ b ∈ fine.names, parent b = a → b = a)
  oldTree : Table n
  oldTree_spans : coarse.quotient.tree oldTree
  localTree : Fin n → Table n
  localTree_spans : ∀ a ∈ refined,
    (quotientRaw (f.induced (coarse.bag a))
      (fine.names.filter (fun b => parent b = a)) fine.bag).tree (localTree a)
  endpoint : Fin n → Fin n → Fin n × Fin n
  endpoint_valid : ∀ a ∈ coarse.names, ∀ b ∈ coarse.names,
    oldTree a b = true →
      (endpoint a b).1 ∈ coarse.bag a ∧ (endpoint a b).2 ∈ coarse.bag b ∧
      f.edges (endpoint a b).1 (endpoint a b).2 = true
  endpoint_symm : ∀ a b, endpoint b a = ((endpoint a b).2, (endpoint a b).1)

noncomputable def Expansion.localGraph {n : ℕ} {f : WeightedGraph n} (x : Expansion f)
    (a : Fin n) : WeightedGraph n :=
  quotientRaw (f.induced (x.coarse.bag a))
    (x.fine.names.filter (fun b => x.parent b = a)) x.fine.bag

/-- Substitute the local trees, attaching each surviving edge at the fine cells containing
its selected original endpoints. The diagonal is explicitly excluded. -/
noncomputable def Expansion.result {n : ℕ} {f : WeightedGraph n} (x : Expansion f) : Table n := by
  classical
  exact fun b c => decide (b ∈ x.fine.names ∧ c ∈ x.fine.names ∧ b ≠ c ∧
    ((x.parent b = x.parent c ∧ x.parent b ∈ x.refined ∧
      x.localTree (x.parent b) b c = true) ∨
     (x.parent b ≠ x.parent c ∧ x.oldTree (x.parent b) (x.parent c) = true ∧
      (x.endpoint (x.parent b) (x.parent c)).1 ∈ x.fine.bag b ∧
      (x.endpoint (x.parent b) (x.parent c)).2 ∈ x.fine.bag c)))

end STCSublinear1377.Main


