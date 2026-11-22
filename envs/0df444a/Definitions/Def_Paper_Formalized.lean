-- Prove2me | Definitions.Def_Paper_Formalized
-- name    : Paper_Formalized
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:49:36.509929+00:00
-- url     : https://prove2.me/theorems/26324863-5cde-4839-9bdd-d52a3f1b38f0
-- title:
--   Formalized
-- statement:
--   Definitions and structural lemmas for Formalized, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean

import Definitions.Def_Paper_TrustBoundary
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace Paper
namespace Hypergraph
def oneBag (H : Hypergraph) : H.TreeDecomposition 0 where
  tree := ⊥
  isTree := by
    letI : Subsingleton (Fin (0 + 1)) := ⟨by intro a b; apply Fin.ext; omega⟩
    exact SimpleGraph.IsTree.of_subsingleton
  bag := fun _ => H.vertices
  bag_subset := fun _ => Subset.refl _
  edge_covered := fun e he => ⟨0, H.edge_subset e he⟩
  vertex_covered := fun v hv => ⟨0, hv⟩
  running_intersection := by
    letI : Subsingleton (Fin (0 + 1)) := ⟨by intro a b; apply Fin.ext; omega⟩
    exact fun _ _ => SimpleGraph.Preconnected.of_subsingleton
theorem coverCost_nonneg (H : Hypergraph) (x : ℕ → ℝ) : 0 ≤ H.coverCost x := by
  unfold coverCost
  by_cases hs : {r : ℝ | ∃ y, H.Cover x y ∧ r = ∑ e ∈ H.edges, y e}.Nonempty
  · apply le_csInf hs
    rintro r ⟨y, hy, rfl⟩
    exact sum_nonneg hy.1
  · rw [Set.not_nonempty_iff_eq_empty.mp hs, Real.sInf_empty]
theorem coverCost_le (H : Hypergraph) {x y : ℕ → ℝ} (hy : H.Cover x y) :
    H.coverCost x ≤ ∑ e ∈ H.edges, y e := by
  refine csInf_le ⟨0, ?_⟩ ⟨y, hy, rfl⟩
  rintro r ⟨z, hz, rfl⟩
  exact sum_nonneg hz.1
theorem coverCost_eq_zero_of_nonpos (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, x v ≤ 0) : H.coverCost x = 0 := by
  apply le_antisymm _ (H.coverCost_nonneg x)
  have hy : H.Cover x (fun _ => 0) := ⟨by simp, by simpa using hx⟩
  simpa using H.coverCost_le hy
def TreeDecomposition.restrict {H : Hypergraph} {n : ℕ}
    (D : H.TreeDecomposition n) (W : Finset ℕ) : (H.induce W).TreeDecomposition n where
  tree := D.tree
  isTree := D.isTree
  bag := fun t => D.bag t ∩ W
  bag_subset := by
    intro t v hv
    exact mem_inter.mpr ⟨D.bag_subset t (mem_inter.mp hv).1, (mem_inter.mp hv).2⟩
  edge_covered := by
    intro e he
    obtain ⟨t, ht⟩ := D.edge_covered e (mem_filter.mp he).1
    exact ⟨t, fun v hv => mem_inter.mpr ⟨ht (mem_inter.mp hv).1, (mem_inter.mp hv).2⟩⟩
  vertex_covered := by
    intro v hv
    obtain ⟨t, ht⟩ := D.vertex_covered v (mem_inter.mp hv).1
    exact ⟨t, mem_inter.mpr ⟨ht, (mem_inter.mp hv).2⟩⟩
  running_intersection := by
    intro v hv
    have hvW := (mem_inter.mp hv).2
    have hs : {t : Fin (n + 1) | v ∈ D.bag t ∩ W} = {t | v ∈ D.bag t} := by
      ext t
      simp only [Set.mem_setOf_eq, mem_inter, hvW, and_true]
    rw [hs]
    exact D.running_intersection v (mem_inter.mp hv).1
def forestGraph {I : Type*} {V : I → Type*} (G : ∀ i, SimpleGraph (V i)) :
    SimpleGraph (Sigma V) where
  Adj a b := ∃ h : a.1 = b.1, (G a.1).Adj a.2 (h.symm ▸ b.2)
  symm := ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨h, hab⟩
    cases h
    exact ⟨rfl, hab.symm⟩⟩
  loopless := ⟨by
    rintro ⟨i, a⟩ ⟨h, ha⟩
    exact (G i).loopless.irrefl a ha⟩
def forestFiberIso {I : Type*} {V : I → Type*} (G : ∀ i, SimpleGraph (V i)) (i : I) :
    ((forestGraph G).induce {a | a.1 = i}) ≃g G i where
  toFun a := a.property ▸ a.val.2
  invFun a := ⟨⟨i, a⟩, rfl⟩
  left_inv := by rintro ⟨⟨j, a⟩, h⟩; cases h; rfl
  right_inv := by intro a; rfl
  map_rel_iff' := by
    rintro ⟨⟨j, a⟩, ha⟩ ⟨⟨k, b⟩, hb⟩
    cases ha
    cases hb
    change (G j).Adj a b ↔ ∃ h : j = j, (G j).Adj a (h.symm ▸ b)
    simp
@[simp] theorem setCoverCost_empty (H : Hypergraph) : H.setCoverCost ∅ = 0 :=
  H.coverCost_eq_zero_of_nonpos (by simp [indicator])
def boundary (H : Hypergraph) (B K : Finset ℕ) : Finset ℕ :=
  B.filter (fun z => ∃ v ∈ K, H.primal.Adj z v)
def TreeDecomposition.ofInduceVertices {H : Hypergraph} {n : ℕ}
    (D : (H.induce H.vertices).TreeDecomposition n) : H.TreeDecomposition n where
  tree := D.tree
  isTree := D.isTree
  bag := D.bag
  bag_subset := fun t v hv => (mem_inter.mp (D.bag_subset t hv)).1
  edge_covered := by
    intro e he
    have heq : H.edge e ∩ H.vertices = H.edge e := inter_eq_left.mpr (H.edge_subset e he)
    have he' : e ∈ (H.induce H.vertices).edges :=
      mem_filter.mpr ⟨he, by rw [heq]; exact H.edge_nonempty e he⟩
    obtain ⟨t,ht⟩ := D.edge_covered e he'
    exact ⟨t, by simpa only [induce,heq] using ht⟩
  vertex_covered := fun v hv => D.vertex_covered v (mem_inter.mpr ⟨hv,hv⟩)
  running_intersection := fun v hv => D.running_intersection v (mem_inter.mpr ⟨hv,hv⟩)
def separatorPathOptions (H : Hypergraph) (e f : ℕ) : Finset (Option (Finset ℕ)) :=
  insert none ((H.vertices.powerset.filter (fun S =>
    ∃ u ∈ H.edge e, ∃ v ∈ H.edge f, ∃ p : H.primal.Walk u v,
      p.IsPath ∧ p.support.toFinset = S)).image some)
def pathOptionCost (o : Option (Finset ℕ)) (x : ℕ → ℝ) : ℝ :=
  o.elim 1 (fun S => ∑ v ∈ S, x v)
def finiteEdgeDistance (H : Hypergraph) (e f : ℕ) (x : ℕ → ℝ) : ℝ :=
  (H.separatorPathOptions e f).inf' (by simp [separatorPathOptions]) (fun o => pathOptionCost o x)
def separatorCube (H : Hypergraph) (γ : ℕ → ℝ) (θ : ℝ) : Set (ℕ → ℝ) :=
  Set.Icc 0 1 ∩ {x | ∀ e ∈ H.edges,
    (1 - θ) * (∑ f ∈ H.edges, γ f) ≤ ∑ f ∈ H.edges, γ f * H.finiteEdgeDistance e f x}
def modularCube (H : Hypergraph) : Set (ℕ → ℝ) :=
  Set.Icc 0 1 ∩ {w | ∀ e ∈ H.edges, ∑ v ∈ H.edge e, w v ≤ 1}
end Hypergraph
end Paper


