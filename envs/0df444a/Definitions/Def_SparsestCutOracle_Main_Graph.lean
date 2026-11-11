-- Prove2me | Definitions.Def_SparsestCutOracle_Main_Graph
-- name    : SparsestCutOracle_Main_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:03.494577+00:00
-- url     : https://prove2.me/theorems/d4c0446d-e45e-4c91-97ae-a912e7ed4818
-- title:
--   Edge-list input, weighted cuts, and induced expansion
-- statement:
--   The general symmetric nonnegative capacity function is the referenced weighted-graph object. A paper-specific input additionally stores a list of loopless edges on $\{0,\ldots,n-1\}$ with nonnegative real capacities, retaining parallel edges. For vertex weights $\pi$, write $\pi(S)=\sum_{v\in S}\pi(v)$ and $\Pi=\pi(V)$.
--
--   For $X\subseteq U$, expansion inside the induced graph means
--
--   $$\pi(X)\le\pi(U\setminus X)\quad\Longrightarrow\quad\operatorname{cap}(X,U\setminus X)\ge q\pi(X).$$
--
--   The input layout contains only edge endpoints, capacities, the weights, and scalar parameters. Connectedness refers to listed edges, including zero-capacity edges in auxiliary results. The main theorem separately requires every capacity to be at least one. Normalized weights are nonnegative, attain one, and have no positive value below one. These definitions distinguish induced expansion from degree conductance.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 3, 7–9, graph and expansion definitions; Theorem 1 input format

import Mathlib
import Definitions.Def_ClusterDecomp_WGraph

namespace SparsestCutOracle.Main

structure Edge (n : ℕ) where
  u : Fin n
  v : Fin n
  capacity : NNReal

/-- Edge lists retain parallel edges, including marked artificial capacity increments. -/
abbrev Graph (n : ℕ) := List (Edge n)

noncomputable def Graph.weight {n : ℕ} (G : Graph n) (u v : Fin n) : ℝ :=
  ∑ i : Fin G.length,
    if (G[i.val].u = u ∧ G[i.val].v = v) ∨ (G[i.val].u = v ∧ G[i.val].v = u)
    then (G[i.val].capacity : ℝ) else 0

noncomputable def Graph.toWGraph {n : ℕ} (G : Graph n) : ClusterDecomp.WGraph (Fin n) where
  w := G.weight
  symm := by intro u v; simp only [Graph.weight, or_comm]
  nonneg := by
    intro u v
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact NNReal.coe_nonneg _
    · exact le_rfl

def Graph.NoLoops {n : ℕ} (G : Graph n) : Prop := ∀ e ∈ G, e.u ≠ e.v

def Graph.UnitLowerBound {n : ℕ} (G : Graph n) : Prop :=
  ∀ e ∈ G, 1 ≤ (e.capacity : ℝ)

noncomputable def Graph.Connected {n : ℕ} (G : Graph n) : Prop :=
  ∀ u v : Fin n, Relation.ReflTransGen
    (fun a b => ∃ e ∈ G, (e.u = a ∧ e.v = b) ∨ (e.u = b ∧ e.v = a)) u v

noncomputable def Graph.total {n : ℕ} (G : Graph n) : ℝ :=
  (G.map fun e => (e.capacity : ℝ)).sum

def mass {n : ℕ} (π : Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∑ v ∈ S, π v

def totalWeight {n : ℕ} (π : Fin n → ℝ) : ℝ := mass π Finset.univ

noncomputable def cut {n : ℕ} (G : ClusterDecomp.WGraph (Fin n))
    (S T : Finset (Fin n)) : ℝ := G.cut S T

/-- Cuts are measured inside U; the two sides are X and U \\ X. -/
def ExpandingOn {n : ℕ} (G : ClusterDecomp.WGraph (Fin n))
    (π : Fin n → ℝ) (U : Finset (Fin n)) (q : ℝ) : Prop :=
  ∀ X : Finset (Fin n), X ⊆ U → mass π X ≤ mass π (U \ X) →
    q * mass π X ≤ cut G X (U \ X)

def NormalizedWeights {n : ℕ} (π : Fin n → ℝ) : Prop :=
  (∀ v, 0 ≤ π v) ∧ (∃ v, π v = 1) ∧ (∀ v, 0 < π v → 1 ≤ π v)

/-- Input integer memory: n,m, then two endpoints for each listed edge.
Real memory: capacities in edge-list order, π(0),...,π(n-1), followed by the scalar parameters.
Only the supplied edge list and weights are encoded, with no precomputed graph information. -/
def graphInts {n : ℕ} (G : Graph n) : List ℤ :=
  [(n : ℤ), (G.length : ℤ)] ++ G.flatMap (fun e => [(e.u.val : ℤ), (e.v.val : ℤ)])

def graphReals {n : ℕ} (G : Graph n) (π : Fin n → ℝ) (params : List ℝ) : List ℝ :=
  G.map (fun e => (e.capacity : ℝ)) ++ (List.finRange n).map π ++ params

end SparsestCutOracle.Main


