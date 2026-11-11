-- Prove2me | Definitions.Def_STCSublinear1377_Main_Laminar
-- name    : STCSublinear1377_Main_Laminar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:36.815096+00:00
-- url     : https://prove2.me/theorems/b6823828-dfdc-4de6-8593-95a50b1defc3
-- title:
--   Algorithm 1 executions, retained names and actual local graphs
-- statement:
--   For a degree threshold $D$, the current hubs of $F$ are $H_F=\{v:d_F(v)>D\}$. Algorithm 1 returns the whole vertex set if there is at most one hub. Otherwise it computes disjoint connected minimum isolating sets, keeps those with boundary at most $D$, fails if none are kept, contracts them, and recursively lifts the returned family. A recursive failure propagates. This execution relation records exactly those operations, without assuming progress, small depth or laminarity.
--
--   A family is laminar when any two members are disjoint or nested. Its depth is the maximum length of an inclusion chain. For a region $R$, let $\mathcal C_R$ be its maximal proper descendants. The graph exposed by Algorithm 2 is
--
--   $$F_R=G[R]/\mathcal C_R,$$
--
--   retaining residual singletons and the names assigned during contraction. A local-call record consists of an actual successful Algorithm 1 execution and one of its regions. The original singleton predicate inspects the bag map itself. This supplies provenance for future local statements; it contains no theorem's desired cut or load bound.
--
--   **Formalization Note** The inductive execution relation is a mathematical operational specification, not a claim that a supplied oracle runs quickly. Lemma 3.2 separately requires an actual polynomial-time evaluator realizing a successful execution.
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Algorithms 1–2 and §3.1–3.2, PDF/printed pp.7–10, Figure 2

import Definitions.Def_STCSublinear1377_Main_Quotient
set_option autoImplicit false

namespace STCSublinear1377.Main

abbrev NamedFamily (n : ℕ) := Finset (Finset (Fin n) × Fin n)

noncomputable def hubs {n : ℕ} (f : WeightedGraph n) (d : ℝ) : Finset (Fin n) := by
  classical
  exact f.vertices.filter (fun v => d < f.degree v)

noncomputable def keptIsolating {n : ℕ} (f : WeightedGraph n) (d : ℝ)
    (sets : Fin n → Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact (hubs f d).filter (fun h => f.boundary (sets h) ≤ d)

noncomputable def liftFamily {n : ℕ} (hs : Finset (Fin n))
    (sets : Fin n → Finset (Fin n)) (l : NamedFamily n) : NamedFamily n := by
  classical
  exact l.image (fun r => (r.1.biUnion (contractionBag hs sets), r.2))

/-- Algorithm 1's finite execution relation. Its only subroutine specification is an exact
connected isolating-cut output; there is no hypothesis about progress, laminarity, depth or
cut preservation. A realizability theorem must supply an actual machine for these executions. -/
inductive LaminarExecution {n : ℕ} : WeightedGraph n → ℝ → Option (NamedFamily n) → Prop
  | base (f : WeightedGraph n) (d : ℝ) (v : Fin n)
      (hv : v ∈ f.vertices) (hh : (hubs f d).card ≤ 1) :
      LaminarExecution f d (some {(f.vertices, v)})
  | fail (f : WeightedGraph n) (d : ℝ) (sets : Fin n → Finset (Fin n))
      (hh : 2 ≤ (hubs f d).card)
      (hi : isolatingSets f (hubs f d) (hubs f d) sets)
      (hc : ∀ v ∈ hubs f d, f.connectedSet (sets v))
      (hk : keptIsolating f d sets = ∅) : LaminarExecution f d none
  | step (f : WeightedGraph n) (d : ℝ) (sets : Fin n → Finset (Fin n))
      (hh : 2 ≤ (hubs f d).card)
      (hi : isolatingSets f (hubs f d) (hubs f d) sets)
      (hc : ∀ v ∈ hubs f d, f.connectedSet (sets v))
      (hk : (keptIsolating f d sets).Nonempty) (l : NamedFamily n)
      (rec : LaminarExecution (contract f (keptIsolating f d sets) sets) d (some l)) :
      LaminarExecution f d (some
        (((keptIsolating f d sets).image (fun h => (sets h, h))) ∪
          liftFamily (keptIsolating f d sets) sets l))
  | propagate (f : WeightedGraph n) (d : ℝ) (sets : Fin n → Finset (Fin n))
      (hh : 2 ≤ (hubs f d).card)
      (hi : isolatingSets f (hubs f d) (hubs f d) sets)
      (hc : ∀ v ∈ hubs f d, f.connectedSet (sets v))
      (hk : (keptIsolating f d sets).Nonempty)
      (rec : LaminarExecution (contract f (keptIsolating f d sets) sets) d none) :
      LaminarExecution f d none

noncomputable def regions {n : ℕ} (l : NamedFamily n) : Finset (Finset (Fin n)) := by
  classical
  exact l.image Prod.fst

noncomputable def laminar {n : ℕ} (l : NamedFamily n) : Prop :=
  ∀ a ∈ regions l, ∀ b ∈ regions l, Disjoint a b ∨ a ⊆ b ∨ b ⊆ a

noncomputable def familyDepth {n : ℕ} (l : NamedFamily n) : ℕ := by
  classical
  exact ((regions l).powerset.filter (fun c =>
    ∀ a ∈ c, ∀ b ∈ c, a ⊆ b ∨ b ⊆ a)).sup Finset.card

noncomputable def residual {n : ℕ} (l : NamedFamily n) (r : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact r \ (((regions l).filter (fun a => a ⊂ r)).biUnion id)

noncomputable def children {n : ℕ} (l : NamedFamily n) (r : Finset (Fin n)) : NamedFamily n := by
  classical
  exact l.filter (fun a => a.1 ⊂ r ∧
    ∀ b ∈ l, a.1 ⊂ b.1 → b.1 ⊂ r → False)

noncomputable def localBags {n : ℕ} (l : NamedFamily n) (r : Finset (Fin n))
    (v : Fin n) : Finset (Fin n) := by
  classical
  let c := (children l r).filter (fun a => a.2 = v)
  exact if c.Nonempty then c.biUnion Prod.fst else {v}

noncomputable def localGraph {n : ℕ} (g : Table n) (l : NamedFamily n)
    (r : Finset (Fin n)) : WeightedGraph n := by
  classical
  let c := children l r
  let names := (r \ c.biUnion Prod.fst) ∪ c.image Prod.snd
  exact quotientRaw ((original g).induced r) names (localBags l r)

/-- The local graphs actually exposed by Algorithm 2, derived from a successful execution of
Algorithm 1. None of the boundary or degree comparisons needed in the analysis are assumed. -/
structure LocalCall {n : ℕ} (g : Table n) (d : ℝ) where
  family : NamedFamily n
  execution : LaminarExecution (original g) d (some family)
  region : Finset (Fin n)
  member : region ∈ regions family

noncomputable def LocalCall.graph {n : ℕ} {g : Table n} {d : ℝ}
    (call : LocalCall g d) : WeightedGraph n := localGraph g call.family call.region

def LocalCall.originalSingleton {n : ℕ} {g : Table n} {d : ℝ}
    (call : LocalCall g d) (h : Fin n) : Prop :=
  h ∈ call.graph.vertices ∧ localBags call.family call.region h = {h}

end STCSublinear1377.Main


