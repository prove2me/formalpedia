-- Prove2me | Definitions.Def_PlanningProphet_Model
-- name    : PlanningProphet_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:58.822994+00:00
-- url     : https://prove2.me/theorems/4b56bb5f-8ec5-4196-945e-4be7fce9d75c
-- title:
--   §2 — DAG with start and target, edge labels with capacities, independent edge values and the prophet $OPT$
-- statement:
--   This module fixes the model of §2 (pp.6–7).
--
--   1. **The graph.** A finite directed acyclic multigraph $G=(V,E)$ with a starting node $s$ and a target node $t$. Parallel edges are allowed: the model asks that every labelled edge have a parallel unlabelled edge.
--   2. **Paths and covers.** An $s,t$-path is a sequence of edges $e_1,\dots,e_m$ with $\mathrm{tail}(e_1)=s$, $\mathrm{head}(e_j)=\mathrm{tail}(e_{j+1})$ and $\mathrm{head}(e_m)=t$; $V(P)$ is the list of nodes it visits, in order. Paths $P_1,\dots,P_k$ **cover** $G$ when each is an $s,t$-path and $V=\bigcup_{i=1}^k V(P_i)$.
--   3. **Labels.** There is a finite label set $L$, each edge carries a set $L_e\subseteq L$, and each label $\ell$ has a capacity $c_\ell$. An edge list $P$ is **feasible** when
--   $$|P\cap E(\ell)|\le c_\ell\qquad\text{for every }\ell\in L,$$
--   where $E(\ell)=\{e: \ell\in L_e\}$. The standing assumptions $c_\ell\ge 1$, $|L_e|\le d$ and "every labelled edge has a parallel unlabelled edge" are predicates used as hypotheses.
--   4. **The prophet.** For values $w\in\mathbb R_{\ge0}^E$,
--   $$OPT(w)=\max\Big\{\sum_{e\in P}w_e \;:\; P \text{ a feasible } s,t\text{-path}\Big\}.$$
--   5. **Correlation.** Random values $W$ on a probability space are **independent across source nodes** when the vectors $(W_e)_{\mathrm{tail}(e)=u}$, $u\in V$, are mutually independent; edges leaving the same node may be arbitrarily correlated.
--
--   Every statement of the mission is made over these objects.
--
--   **Formalization Note** The multigraph, its walks (`IsPathFrom`) and acyclicity (no nonempty closed walk) are the published `AtomicDynRouting.ResidenceTime.Network`. Path values are computed in $[0,\infty]$, so that expectations are lower Lebesgue integrals. $OPT$ is a supremum in $[0,\infty]$; it is a maximum whenever a feasible $s,t$-path exists. The paper's $L_e\subset L$ is read as $L_e\subseteq L$.
-- source:
--   Cristi, Oren, Planning Against a Prophet: A Graph-Theoretic Framework for Making Sequential Decisions, arXiv:2406.13911v1, §2 Model, pp.6–7: DAG and values p.6; OPT display, Correlation, Path Covering, Edge Labels and footnote 2, p.7

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace PlanningProphet

/-! # The model of §2 (Cristi–Oren, *Planning Against a Prophet*, arXiv:2406.13911v1, pp.6–7)

A directed acyclic multigraph with a start node `s` and a target node `t`, labelled edges with
label capacities, nonnegative random edge values that are independent across source nodes, the
`s,t`-paths, path covers, label feasibility, and the prophet's value `OPT`.

**Formalization Note.**
1. The multigraph is the published `AtomicDynRouting.ResidenceTime.Network` (edges form a type,
   `tail e` and `head e` are the endpoints, so parallel edges are allowed, as the paper's model
   requires: "for every labeled edge, there is a parallel unlabeled edge", p.7). Its `IsPathFrom`
   (an edge list chaining from one node to another) and `Acyclic` (no nonempty closed walk) are the
   paths and the DAG condition. In an acyclic graph every walk is a path.
2. A path is the list of its edges in order. `V(P)` is `s` followed by the heads of the edges.
3. Values are `w : E → ℝ≥0` (nonnegative, §2); path values are computed in `ℝ≥0∞`, so that
   expectations are lower Lebesgue integrals and need no integrability hypothesis.
4. `OPT` is the supremum, in `ℝ≥0∞`, of the values of the label-feasible `s,t`-paths. In a finite
   acyclic graph there are finitely many `s,t`-paths, so the supremum is a maximum whenever one
   feasible `s,t`-path exists (under the theorems' hypotheses a cover path with its labelled edges
   swapped for their unlabelled parallels is one). With no label (`labels e = ∅` for all `e`)
   every `s,t`-path is feasible and `OPT` is the paper's unlabelled `max_{P ∈ 𝒫} Σ_{e ∈ P} w_e`. -/

open AtomicDynRouting.ResidenceTime

/-- The value `Σ_{e ∈ P} w_e` of an edge list, in `ℝ≥0∞`. -/
def pathValue {E : Type} (w : E → ℝ≥0) (p : List E) : ℝ≥0∞ := (p.map fun e => (w e : ℝ≥0∞)).sum

/-- The graph of §2 (arXiv:2406.13911v1, pp.6–7): a directed multigraph `(V, E)` with endpoints
`tail`, `head`, a starting node `s`, a target node `t`, for each edge `e` a set of labels
`L_e ⊆ L` and for each label `ℓ` a capacity `c_ℓ`.

**Formalization Note.** Finiteness of `V`, `E`, `L`, acyclicity, `c_ℓ ≥ 1` and the parallel
unlabelled edges are hypotheses of each theorem (`Acyclic`, `CapPos`, `ParallelUnlabeled` below).
The paper's `L_e ⊂ L` is read as `⊆`. The unlabelled model of §2 is the case `labels e = ∅`. -/
structure Graph (V E L : Type) extends Network V E where
  /-- The starting node `s`. -/
  s : V
  /-- The target node `t`. -/
  t : V
  /-- The label set `L_e` of each edge. -/
  labels : E → Finset L
  /-- The capacity `c_ℓ` of each label. -/
  cap : L → ℕ

namespace Graph

variable {V E L : Type} (G : Graph V E L)

/-- `P` is an `s,t`-path (p.7, the set `𝒫`): its edges chain from `s` to `t`. The empty list is
an `s,t`-path exactly when `s = t`. -/
def IsSTPath (p : List E) : Prop := G.toNetwork.IsPathFrom G.s G.t p

/-- `V(P)`, the nodes visited by the edge list `P` starting at `s`, in the order visited (p.7):
`s` followed by the heads of the edges. -/
def vertices (p : List E) : List V := G.s :: p.map G.head

/-- The node reached after following the edge list `p` from `s`: the head of its last edge, and
`s` for the empty list. -/
def current (p : List E) : V := (p.getLast?.map G.head).getD G.s

/-- The graph is a DAG (§2): no nonempty closed walk. -/
def Acyclic : Prop := G.toNetwork.Acyclic

/-- `P₁, …, P_k` cover the graph (p.7): each `Pᵢ` is an `s,t`-path and `V = ⋃ᵢ V(Pᵢ)`. -/
def CoveredBy {k : ℕ} (P : Fin k → List E) : Prop :=
  (∀ i, G.IsSTPath (P i)) ∧ ∀ v, ∃ i, v ∈ G.vertices (P i)

/-- `|P ∩ E(ℓ)|`: the number of edges of `p` that carry the label `ℓ` (p.7). -/
def labelCount [DecidableEq L] (p : List E) (ℓ : L) : ℕ :=
  (p.filter fun e => decide (ℓ ∈ G.labels e)).length

/-- The label constraint (p.7): `|P ∩ E(ℓ)| ≤ c_ℓ` for every label `ℓ`. -/
def LabelFeasible [DecidableEq L] (p : List E) : Prop := ∀ ℓ, G.labelCount p ℓ ≤ G.cap ℓ

/-- Each edge has at most `d` labels: `|L_e| ≤ d` (Theorems 3 and 4). -/
def LabelsAtMost (d : ℕ) : Prop := ∀ e, (G.labels e).card ≤ d

/-- Every capacity is at least one: `c_ℓ ≥ 1` (p.7). -/
def CapPos : Prop := ∀ ℓ, 1 ≤ G.cap ℓ

/-- For every labelled edge there is a parallel unlabelled edge (p.7). -/
def ParallelUnlabeled : Prop :=
  ∀ e, G.labels e ≠ ∅ → ∃ e', G.tail e' = G.tail e ∧ G.head e' = G.head e ∧ G.labels e' = ∅

/-- `v` can be reached from `u` by a directed walk (possibly empty). -/
def Reach (u v : V) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ e, G.tail e = a ∧ G.head e = b) u v

/-- `OPT` (p.7): the largest value of a label-feasible `s,t`-path ("We also impose that `OPT`
satisfies the same constraint"), `max_{P ∈ 𝒫} Σ_{e ∈ P} w_e`. It is `0` if there is no feasible
`s,t`-path, which the theorems' hypotheses exclude. -/
noncomputable def opt [DecidableEq L] (w : E → ℝ≥0) : ℝ≥0∞ :=
  ⨆ (p : List E) (_ : G.IsSTPath p ∧ G.LabelFeasible p), pathValue w p

/-- Independence across source nodes (§2, "Correlation", p.7): the vectors
`(W e)_{e : tail e = u}` of the values of the edges leaving `u`, for `u ∈ V`, are mutually
independent. Nothing is assumed about the joint law of the edges leaving one node ("Edges that
start in the same node can be arbitrarily correlated"). -/
def IndepAcrossNodes {Ω : Type*} [MeasurableSpace Ω] (W : Ω → E → ℝ≥0) (μ : Measure Ω) : Prop :=
  iIndepFun (fun (u : V) (ω : Ω) (e : {e : E // G.tail e = u}) => W ω e.1) μ

end Graph

end PlanningProphet


