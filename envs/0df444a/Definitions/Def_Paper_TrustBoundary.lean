-- Prove2me | Definitions.Def_Paper_TrustBoundary
-- name    : Paper_TrustBoundary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:49:16.395638+00:00
-- url     : https://prove2.me/theorems/8957ce7a-7f59-42fa-b02a-dbe0724ee6cb
-- title:
--   Trust Boundary
-- statement:
--   Definitions and structural lemmas for Trust Boundary, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TrustBoundary.lean

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Topology.Sion
import Mathlib.Tactic
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace Paper
structure Hypergraph where
  vertices : Finset ℕ
  edges : Finset ℕ
  edge : ℕ → Finset ℕ
  edge_subset : ∀ e ∈ edges, edge e ⊆ vertices
  edge_nonempty : ∀ e ∈ edges, (edge e).Nonempty
  no_isolated : ∀ v ∈ vertices, ∃ e ∈ edges, v ∈ edge e
namespace Hypergraph
def induce (H : Hypergraph) (W : Finset ℕ) : Hypergraph where
  vertices := H.vertices ∩ W
  edges := H.edges.filter fun e => (H.edge e ∩ W).Nonempty
  edge := fun e => H.edge e ∩ W
  edge_subset := by
    intro e he v hv
    exact mem_inter.mpr ⟨H.edge_subset e (mem_filter.mp he).1 (mem_inter.mp hv).1,
      (mem_inter.mp hv).2⟩
  edge_nonempty := by
    intro e he
    exact (mem_filter.mp he).2
  no_isolated := by
    intro v hv
    obtain ⟨e, he, hve⟩ := H.no_isolated v (mem_inter.mp hv).1
    have hv' : v ∈ H.edge e ∩ W := mem_inter.mpr ⟨hve, (mem_inter.mp hv).2⟩
    exact ⟨e, mem_filter.mpr ⟨he, ⟨v, hv'⟩⟩, hv'⟩
def primal (H : Hypergraph) : SimpleGraph ℕ where
  Adj u v := u ≠ v ∧ ∃ e ∈ H.edges, u ∈ H.edge e ∧ v ∈ H.edge e
  symm := by
    constructor
    rintro u v ⟨huv, e, he, hu, hv⟩
    exact ⟨huv.symm, e, he, hv, hu⟩
  loopless := ⟨by simp⟩
def incidence (H : Hypergraph) : SimpleGraph (ℕ ⊕ ℕ) where
  Adj a b := match a, b with
    | .inl v, .inr e => e ∈ H.edges ∧ v ∈ H.edge e
    | .inr e, .inl v => e ∈ H.edges ∧ v ∈ H.edge e
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp⟩
  loopless := ⟨by intro a; cases a <;> simp⟩
def incidenceVertices (H : Hypergraph) : Finset (ℕ ⊕ ℕ) :=
  H.vertices.map Function.Embedding.inl ∪ H.edges.map Function.Embedding.inr
def degeneracy (H : Hypergraph) : ℕ := sInf {d | ∀ S ⊆ H.incidenceVertices,
  S.Nonempty → ∃ v ∈ S, (S.filter (H.incidence.Adj v)).card ≤ d}
def independent (H : Hypergraph) (S : Finset ℕ) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ H.primal.Adj u v
def independenceNumber (H : Hypergraph) : ℕ :=
  (H.vertices.powerset.filter H.independent).sup Finset.card
def components (H : Hypergraph) : Finset (Finset ℕ) :=
  H.vertices.powerset.filter fun C => ∃ v ∈ C,
    ∀ w ∈ H.vertices, w ∈ C ↔ H.primal.Reachable v w
def Connected (H : Hypergraph) : Prop :=
  H.vertices.Nonempty ∧ ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Reachable u v
def structuralFactor (H : Hypergraph) : ℝ :=
  1 + min (H.degeneracy : ℝ) (Real.log (2 + (H.independenceNumber : ℝ)))
def componentFactor (H : Hypergraph) : ℝ :=
  1 + sSup (insert 0 {r | ∃ C ∈ H.components,
    r = min ((H.induce C).degeneracy : ℝ)
      (Real.log (2 + ((H.induce C).independenceNumber : ℝ)))})
def lambda (H : Hypergraph) : ℝ :=
  min (H.degeneracy : ℝ) (max 1 (Real.log (H.independenceNumber : ℝ) / Real.log 2))
def Cover (H : Hypergraph) (x y : ℕ → ℝ) : Prop :=
  (∀ e ∈ H.edges, 0 ≤ y e) ∧
  ∀ v ∈ H.vertices, x v ≤ ∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), y e
def coverCost (H : Hypergraph) (x : ℕ → ℝ) : ℝ :=
  sInf {r | ∃ y, H.Cover x y ∧ r = ∑ e ∈ H.edges, y e}
def indicator (S : Finset ℕ) (v : ℕ) : ℝ := if v ∈ S then 1 else 0
def setCoverCost (H : Hypergraph) (S : Finset ℕ) : ℝ := H.coverCost (indicator S)
def ModularWeight (H : Hypergraph) (w : ℕ → ℝ) : Prop :=
  (∀ v, 0 ≤ w v) ∧ ∀ e ∈ H.edges, ∑ v ∈ H.edge e, w v ≤ 1
def modularValue (w : ℕ → ℝ) (S : Finset ℕ) : ℝ := ∑ v ∈ S, w v
def SubmodularWeight (H : Hypergraph) (b : Finset ℕ → ℝ) : Prop :=
  b ∅ = 0 ∧
  (∀ A ⊆ H.vertices, ∀ B ⊆ H.vertices, A ⊆ B → b A ≤ b B) ∧
  (∀ A ⊆ H.vertices, ∀ B ⊆ H.vertices, b (A ∪ B) + b (A ∩ B) ≤ b A + b B) ∧
  ∀ e ∈ H.edges, b (H.edge e) ≤ 1
structure TreeDecomposition (H : Hypergraph) (n : ℕ) where
  tree : SimpleGraph (Fin (n + 1))
  isTree : tree.IsTree
  bag : Fin (n + 1) → Finset ℕ
  bag_subset : ∀ t, bag t ⊆ H.vertices
  edge_covered : ∀ e ∈ H.edges, ∃ t, H.edge e ⊆ bag t
  vertex_covered : ∀ v ∈ H.vertices, ∃ t, v ∈ bag t
  running_intersection : ∀ v ∈ H.vertices,
    (tree.induce {t | v ∈ bag t}).Preconnected
def TreeDecomposition.bagWidth {H : Hypergraph} {n : ℕ} (D : H.TreeDecomposition n)
    (b : Finset ℕ → ℝ) : ℝ := sSup (Set.range fun t => b (D.bag t))
def optimalWidth (H : Hypergraph) (b : Finset ℕ → ℝ) : ℝ :=
  sInf {r | ∃ n, ∃ D : H.TreeDecomposition n, r = D.bagWidth b}
def fhw (H : Hypergraph) : ℝ := H.optimalWidth H.setCoverCost
def adw (H : Hypergraph) : ℝ :=
  sSup {r | ∃ w, H.ModularWeight w ∧ r = H.optimalWidth (modularValue w)}
def subw (H : Hypergraph) : ℝ :=
  sSup {r | ∃ b, H.SubmodularWeight b ∧ r = H.optimalWidth b}
def UnitDemand (H : Hypergraph) (x : ℕ → ℝ) : Prop :=
  ∀ v ∈ H.vertices, 0 ≤ x v ∧ x v ≤ 1
def EdgeWeight (H : Hypergraph) (γ : ℕ → ℝ) : Prop :=
  (∀ e ∈ H.edges, 0 ≤ γ e ∧ γ e ≤ 1) ∧ 0 < ∑ e ∈ H.edges, γ e
def vertexDistance (H : Hypergraph) (x : ℕ → ℝ) (u v : ℕ) : ℝ :=
  sInf (insert 1 {r | ∃ p : H.primal.Walk u v, p.IsPath ∧
    r = ∑ z ∈ p.support.toFinset, x z})
def edgeDistance (H : Hypergraph) (x : ℕ → ℝ) (e f : ℕ) : ℝ :=
  sInf {r | ∃ u ∈ H.edge e, ∃ v ∈ H.edge f, r = H.vertexDistance x u v}
def FractionalBalanced (H : Hypergraph) (γ : ℕ → ℝ) (θ : ℝ) (x : ℕ → ℝ) : Prop :=
  H.UnitDemand x ∧ ∀ e ∈ H.edges,
    (1 - θ) * (∑ f ∈ H.edges, γ f) ≤ ∑ f ∈ H.edges, γ f * H.edgeDistance x e f
def IntegralBalanced (H : Hypergraph) (γ : ℕ → ℝ) (θ : ℝ) (S : Finset ℕ) : Prop :=
  S ⊆ H.vertices ∧ ∀ K ∈ (H.induce (H.vertices \ S)).components,
    (∑ e ∈ H.edges.filter (fun e => ¬ Disjoint (H.edge e) K), γ e) ≤
      θ * ∑ e ∈ H.edges, γ e
def beta (H : Hypergraph) (θ : ℝ) (γ : ℕ → ℝ) : ℝ :=
  sInf {r | ∃ x, H.FractionalBalanced γ θ x ∧ r = H.coverCost x}
def integralOptimum (H : Hypergraph) (θ : ℝ) (γ : ℕ → ℝ) : ℝ :=
  sInf {r | ∃ S, H.IntegralBalanced γ θ S ∧ r = H.setCoverCost S}
def fsep (H : Hypergraph) (θ : ℝ) : ℝ :=
  sSup (insert 0 {r | ∃ W ⊆ H.vertices, ∃ γ, (H.induce W).EdgeWeight γ ∧
    r = (H.induce W).beta θ γ})
def sep (H : Hypergraph) (θ : ℝ) : ℝ :=
  sSup (insert 0 {r | ∃ W ⊆ H.vertices, ∃ γ, (H.induce W).EdgeWeight γ ∧
    r = (H.induce W).integralOptimum θ γ})
def BalancedRounding : Prop :=
  ∀ (H : Hypergraph) (γ x : ℕ → ℝ) (φ : ℝ)
    (_hφ : 0 < φ ∧ φ < 1)
    (_hγ : ∀ e ∈ H.edges, 0 ≤ γ e ∧ γ e ≤ 1)
    (_hx : H.FractionalBalanced γ φ x)
    (_hnontrivial : ¬ H.IntegralBalanced γ ((1 + 3 * φ) / (2 + 2 * φ)) ∅),
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0),
      H.IntegralBalanced γ ((1 + 3 * φ) / (2 + 2 * φ)) S ∧
      H.setCoverCost S ≤
        (min (8 + 4 * Real.log
          ((H.induce (H.vertices.filter (fun v => x v ≠ 0))).independenceNumber : ℝ))
          (6 * (H.degeneracy : ℝ)) + 1) *
        ((44 + 8 * (Real.log (H.coverCost x / (1 - φ)) / Real.log 2)) / (1 - φ)) *
        H.coverCost x
def MainWidthComparison : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ H : Hypergraph,
    H.vertices.Nonempty →
    (2 ≤ H.adw → H.fhw ≤ C * H.lambda * H.adw *
      (Real.log H.adw / Real.log 2)) ∧
    (H.adw < 2 → H.fhw ≤ C * H.lambda)
end Hypergraph
end Paper


