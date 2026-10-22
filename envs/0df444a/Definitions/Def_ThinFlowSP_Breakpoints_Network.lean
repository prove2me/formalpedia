-- Prove2me | Definitions.Def_ThinFlowSP_Breakpoints_Network
-- name    : ThinFlowSP_Breakpoints_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:08.151599+00:00
-- url     : https://prove2.me/theorems/6dd5c80b-dbcf-4fba-85e7-329be95351b2
-- title:
--   Definitions 3, 5, 10, 27, 28 — two-terminal multigraphs, static flows, incidence and Laplacian matrices, series-parallel terms
-- statement:
--   This file sets up the graph layer used throughout Kaiser's analysis of normalized thin flows.
--
--   A **network** $G$ is a finite directed multigraph: a finite vertex set $V$, a finite arc set $A'$, maps assigning to each arc $a$ its tail and its head, and two distinguished vertices, the source $s$ and the sink $t$. Parallel arcs (several arcs with the same tail and head) are allowed. For a vertex $v$, $\delta^-(v)$ and $\delta^+(v)$ are the arcs entering and leaving $v$.
--
--   1. $G$ is **acyclic** if it has no directed closed walk of positive length, and $v$ is **reachable** from $u$ if there is a directed $u$–$v$-path.
--   2. (Definition 3, arc part.) $G$ is a **shortest path graph** if it is acyclic and every vertex is reachable from $s$. The set $A^* \subseteq A'$ of resetting arcs, which completes the triple $(V, A', A^*)$ of Definition 3, is passed separately where it is needed.
--   3. (Definition 27.) $G$ is a **two-terminal directed acyclic graph** if it is acyclic, $s$ is the only vertex without entering arcs and $t$ is the only vertex without leaving arcs.
--   4. A **static $s$–$t$-flow of value** $\nu'_0$ is a vector $x \in \mathbb R^{A'}$ with $x \ge 0$, flow conservation at every $v \notin \{s,t\}$, and net outflow $\nu'_0$ at $s$:
--   $$\sum_{a\in\delta^+(v)} x_a - \sum_{a\in\delta^-(v)} x_a = \begin{cases}\nu'_0 & v = s,\\ 0 & v \in V\setminus\{s,t\}.\end{cases}$$
--   5. (Definition 5.) The **incidence matrix** $B \in \{-1,0,1\}^{V\times A'}$ has $B_{v,a} = 1$ if $a \in \delta^-(v)$, $B_{v,a} = -1$ if $a \in \delta^+(v)$, and $0$ otherwise; $B^+$ and $B^-$ are its positive and negative parts, so $B = B^+ - B^-$.
--   6. (Definition 10.) For arc weights $\nu$, the **weighted Laplacian** $L \in \mathbb R^{V\times V}$ has $L_{v,v} = \sum_{a \in \delta^-(v)} \nu_a$ and, for $v \ne w$, $L_{v,w} = -\nu_{v,w}$, the negative total weight of the arcs from $v$ to $w$ (zero if there is none).
--   7. (Definition 28.) The **series composition** $G_1 * G_2$ glues the sink of $G_1$ to the source of $G_2$; its source is $s_{G_1}$, its sink $t_{G_2}$, and its arc set the disjoint union of the two arc sets. The **parallel composition** $G_1 \parallel G_2$ glues the two sources together and the two sinks together. The **two-terminal series-parallel** multigraphs are generated from the single arc $s \to t$ by these two operations; they are represented by terms built from `arc`, `series` and `par`.
--
--   These are the combinatorial objects on which normalized thin flows with resetting, their linear complementarity formulation and the breakpoint count for series-parallel networks are stated.
--
--   **Formalization Note** Arcs are elements of an arc type with tail and head maps, so the graph is a multigraph; Definition 3's "$A' \subseteq V\times V$" is the simple-graph case, while Definitions 27–28 and Example 16 of the paper need parallel arcs. In a composition, the vertices of $G_2$ are embedded by identifying $s_{G_2}$ with $t_{G_1}$ (series), resp. $s_{G_2}$ with $s_{G_1}$ and $t_{G_2}$ with $t_{G_1}$ (parallel). The class of Definition 28 is closed under isomorphism only implicitly: every member is isomorphic to the graph of a term, and every quantity in this mission is invariant under isomorphism. $B^+$ and $B^-$ are taken literally as positive and negative parts (a self-loop has a zero column).
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, pp. 3–5, 8, 18, Definitions 3, 5, 10, 27, 28; static flow p. 5

import Mathlib

namespace ThinFlowSP.Breakpoints

/-- A finite directed multigraph with a source `s` and a sink `t`. Arcs are elements of the
type `A`; arc `a` goes from `tail a` to `head a`. Two arcs with the same endpoints are distinct
elements of `A` (parallel arcs are allowed, as in Definitions 27–28 of Kaiser). -/
structure Net where
  V : Type
  A : Type
  [fV : Fintype V]
  [dV : DecidableEq V]
  [fA : Fintype A]
  [dA : DecidableEq A]
  tail : A → V
  head : A → V
  s : V
  t : V

attribute [instance] Net.fV Net.dV Net.fA Net.dA

/-- `Adj G u v`: there is an arc from `u` to `v`. -/
def Adj (G : Net) (u v : G.V) : Prop := ∃ a, G.tail a = u ∧ G.head a = v

/-- The arc set is acyclic: no directed closed walk of positive length. -/
def IsAcyclic (G : Net) : Prop := ∀ v, ¬ Relation.TransGen (Adj G) v v

/-- `Reaches G u v`: there is a directed `u`–`v`-path (possibly of length zero). -/
def Reaches (G : Net) (u v : G.V) : Prop := Relation.ReflTransGen (Adj G) u v

/-- Definition 3 (shortest path graph with resetting), arc part: the arcs `A′` (all arcs of `G`)
are acyclic and contain an `s`–`v`-path for every vertex `v`. The resetting arcs `A* ⊆ A′` are
passed separately as a `Finset G.A`. -/
def IsShortestPathGraph (G : Net) : Prop := IsAcyclic G ∧ ∀ v, Reaches G G.s v

/-- Definition 27 (two-terminal directed graph): an acyclic multigraph whose unique vertex
without incoming arcs is `s` and whose unique vertex without outgoing arcs is `t`. -/
def IsTwoTerminalDAG (G : Net) : Prop :=
  IsAcyclic G ∧ (∀ v, (∀ a, G.head a ≠ v) ↔ v = G.s) ∧ (∀ v, (∀ a, G.tail a ≠ v) ↔ v = G.t)

/-- Total flow on the arcs entering `v` (the arcs of `δ⁻(v)`). -/
def inflow (G : Net) (x : G.A → ℝ) (v : G.V) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a => G.head a = v), x a

/-- Total flow on the arcs leaving `v` (the arcs of `δ⁺(v)`). -/
def outflow (G : Net) (x : G.A → ℝ) (v : G.V) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a => G.tail a = v), x a

/-- A static `s`–`t`-flow of value `val`: non-negative on every arc, conserved at every vertex
other than `s` and `t`, and with net outflow `val` at `s`. -/
def IsStaticFlow (G : Net) (x : G.A → ℝ) (val : ℝ) : Prop :=
  (∀ a, 0 ≤ x a) ∧
  (∀ v, v ≠ G.s → v ≠ G.t → outflow G x v - inflow G x v = 0) ∧
  outflow G x G.s - inflow G x G.s = val

/-- Definition 5: the directed incidence matrix, `B v a = -1` if `a ∈ δ⁺(v)`, `1` if
`a ∈ δ⁻(v)`, `0` otherwise (a self-loop at `v` gets `0`). -/
def incidence (G : Net) : Matrix G.V G.A ℝ :=
  Matrix.of fun v a => (if G.head a = v then 1 else 0) - (if G.tail a = v then 1 else 0)

/-- The positive part `B⁺` of the incidence matrix. -/
def incPos (G : Net) : Matrix G.V G.A ℝ := Matrix.of fun v a => max (incidence G v a) 0

/-- The negative part `B⁻` of the incidence matrix, so that `B = B⁺ - B⁻`. -/
def incNeg (G : Net) : Matrix G.V G.A ℝ := Matrix.of fun v a => max (-incidence G v a) 0

/-- Definition 10: the weighted directed Laplacian. `L v v` is the total weight of the arcs
entering `v`; for `v ≠ w`, `L v w` is minus the total weight of the arcs from `v` to `w`
(the multigraph reading of `-ν_{v,w}`; `0` if there is none). -/
def laplacian (G : Net) (ν : G.A → ℝ) : Matrix G.V G.V ℝ :=
  Matrix.of fun v w =>
    if v = w then ∑ a ∈ Finset.univ.filter (fun a => G.head a = v), ν a
    else -∑ a ∈ Finset.univ.filter (fun a => G.tail a = v ∧ G.head a = w), ν a

/-- The graph with two vertices `s = false`, `t = true` and a single arc between them. -/
def Net.arc : Net where
  V := Bool
  A := Unit
  tail _ := false
  head _ := true
  s := false
  t := true

/-- Embedding of the vertices of `G₂` into the series composition: `s_{G₂}` is identified
with `t_{G₁}`. -/
def seriesEmb (G₁ G₂ : Net) (v : G₂.V) : G₁.V ⊕ {v : G₂.V // v ≠ G₂.s} :=
  if h : v = G₂.s then Sum.inl G₁.t else Sum.inr ⟨v, h⟩

/-- Definition 28, series composition `G₁ ∗ G₂`: disjoint union of the arcs, vertex sets
glued along `t_{G₁} = s_{G₂}`, source `s_{G₁}`, sink `t_{G₂}`. -/
def Net.series (G₁ G₂ : Net) : Net where
  V := G₁.V ⊕ {v : G₂.V // v ≠ G₂.s}
  A := G₁.A ⊕ G₂.A
  tail := Sum.elim (fun a => Sum.inl (G₁.tail a)) (fun a => seriesEmb G₁ G₂ (G₂.tail a))
  head := Sum.elim (fun a => Sum.inl (G₁.head a)) (fun a => seriesEmb G₁ G₂ (G₂.head a))
  s := Sum.inl G₁.s
  t := seriesEmb G₁ G₂ G₂.t

/-- Embedding of the vertices of `G₂` into the parallel composition: `s_{G₂}` is identified
with `s_{G₁}` and `t_{G₂}` with `t_{G₁}`. -/
def parEmb (G₁ G₂ : Net) (v : G₂.V) : G₁.V ⊕ {v : G₂.V // v ≠ G₂.s ∧ v ≠ G₂.t} :=
  if h₁ : v = G₂.s then Sum.inl G₁.s
  else if h₂ : v = G₂.t then Sum.inl G₁.t
  else Sum.inr ⟨v, h₁, h₂⟩

/-- Definition 28, parallel composition `G₁ ∥ G₂`: disjoint union of the arcs, vertex sets
glued along `s_{G₁} = s_{G₂}` and `t_{G₁} = t_{G₂}`. -/
def Net.par (G₁ G₂ : Net) : Net where
  V := G₁.V ⊕ {v : G₂.V // v ≠ G₂.s ∧ v ≠ G₂.t}
  A := G₁.A ⊕ G₂.A
  tail := Sum.elim (fun a => Sum.inl (G₁.tail a)) (fun a => parEmb G₁ G₂ (G₂.tail a))
  head := Sum.elim (fun a => Sum.inl (G₁.head a)) (fun a => parEmb G₁ G₂ (G₂.head a))
  s := Sum.inl G₁.s
  t := Sum.inl G₁.t

/-- Terms generating the two-terminal series-parallel directed graphs (Definition 28):
a single arc, series composition, parallel composition. -/
inductive SPTerm
  | arc
  | series (T₁ T₂ : SPTerm)
  | par (T₁ T₂ : SPTerm)

/-- The two-terminal series-parallel multigraph denoted by a term. -/
def SPTerm.toNet : SPTerm → Net
  | .arc => Net.arc
  | .series T₁ T₂ => T₁.toNet.series T₂.toNet
  | .par T₁ T₂ => T₁.toNet.par T₂.toNet

end ThinFlowSP.Breakpoints


