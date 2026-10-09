-- Prove2me | Definitions.Def_ConstATSP_Gap_Graph
-- name    : ConstATSP_Gap_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:51.824532+00:00
-- url     : https://prove2.me/theorems/b1fa1649-f931-41ea-90a5-143c6560316e
-- title:
--   Def. 1.2, Def. 2.1, §2.1, pp. 4–8 — digraphs with parallel edges, cuts, Eulerian multisets, subtours and tours, LP(G, w) and DUAL(G, w)
-- statement:
--   This file fixes the graph-theoretic setting of the asymmetric traveling salesman problem (ATSP) and of its Held–Karp relaxation.
--
--   1. A **digraph** $G=(V,E)$ has a finite vertex set $V$ and a finite edge set $E$; each edge $e$ has a tail and a head. Parallel edges and loops are allowed. For $S\subseteq V$, $\delta^+(S)$ is the set of edges leaving $S$, $\delta^-(S)$ the set of edges entering $S$, and $\delta(S)=\delta^+(S)\cup\delta^-(S)$; a loop lies in no cut. $G$ is **strongly connected** if every vertex reaches every vertex along directed edges, and a set $U$ **induces a strongly connected subgraph** if this holds using only edges with both endpoints in $U$.
--   2. An **edge multiset** $F$ assigns a multiplicity $F(e)\in\mathbb N$ to every edge. $V(F)$ is the set of vertices incident to an edge of positive multiplicity. $F$ is **Eulerian** if $|\delta^+_F(v)|=|\delta^-_F(v)|$ for every vertex $v$, counted with multiplicity. $F$ is a **subtour** if it is Eulerian and the graph $(V(F),F)$ is connected (the empty multiset is a subtour), and a **tour** if moreover $V(F)=V$. The **subtours in** an Eulerian $F$ are the connected components of $(V(F),F)$.
--   3. The **asymmetric Held–Karp relaxation** LP$(G,w)$ is
--   $$\min \sum_{e\in E} w(e)x(e)\quad\text{s.t.}\quad x(\delta^+(v))=x(\delta^-(v))\ (v\in V),\qquad x(\delta(S))\ge 2\ (\emptyset\ne S\subsetneq V),\qquad x\ge 0 .$$
--   Its optimum is the **Held–Karp lower bound**. Feasibility does not depend on $w$, so it is also feasibility for LP$(G,0)$.
--   4. The dual DUAL$(G,w)$ maximizes $\sum_{\emptyset\ne S\subsetneq V}2y_S$ subject to $\sum_{S:\,e\in\delta(S)}y_S+\alpha_u-\alpha_v\le w(e)$ for every edge $e=(u,v)$ and $y\ge 0$.
--   5. A family of vertex sets is **laminar** if any two of its members are nested or disjoint.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Edges are a type `E` with tail and head maps, so parallel copies are distinct edges, as in the paper's contraction (§2, p. 7: "We keep all parallel copies"). Edge multisets are functions `E → ℕ`. Connectivity of $(V(F),F)$ and components are expressed by the reflexive–transitive closure of undirected adjacency along edges of $F$. The Held–Karp lower bound is never introduced as a number: statements that compare with it quantify over all feasible $x$. The dual potentials are called `a` (the paper's $\alpha$), and the dual variables `y` are a function on all vertex sets of which only proper nonempty sets are read.
-- source:
--   Svensson, Tarnawski, Végh, A constant-factor approximation algorithm for the asymmetric traveling salesman problem, J. ACM 67(6) (2020), accepted manuscript (LSE Research Online 106582), pp. 4–8, Definition 1.2, §2 (notation), Definition 2.1, §2.1 (LP(G, w), DUAL(G, w), laminar families)

import Mathlib

namespace ConstATSP.Gap

/-- A directed graph with possibly parallel edges and loops (Def. 1.2, §2, pp. 4–7): every edge `e : E`
has a tail `src e` and a head `tgt e`. -/
structure Graph (V E : Type) where
  /-- the tail of an edge -/
  src : E → V
  /-- the head of an edge -/
  tgt : E → V

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

/-- `δ⁺(S)`: the edges leaving `S` (§2, p. 6). A loop is in no cut. -/
def outE (G : Graph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (fun e => G.src e ∈ S ∧ G.tgt e ∉ S)

/-- `δ⁻(S)`: the edges entering `S` (§2, p. 6). -/
def inE (G : Graph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (fun e => G.src e ∉ S ∧ G.tgt e ∈ S)

/-- `δ(S) = δ⁻(S) ∪ δ⁺(S)`: the boundary edges of `S`, those with exactly one endpoint in `S`
(§2, p. 6). -/
def bdE (G : Graph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (fun e => (G.src e ∈ S ∧ G.tgt e ∉ S) ∨ (G.src e ∉ S ∧ G.tgt e ∈ S))

/-- `G` is strongly connected: every vertex reaches every vertex along directed edges. -/
def IsStronglyConnected (G : Graph V E) : Prop :=
  ∀ u v : V, Relation.ReflTransGen (fun a b => ∃ e, G.src e = a ∧ G.tgt e = b) u v

/-- The subgraph `G[U]` induced by `U` is strongly connected: every vertex of `U` reaches every vertex of
`U` along directed edges with both endpoints in `U`. -/
def IsStronglyConnectedOn (G : Graph V E) (U : Finset V) : Prop :=
  ∀ u ∈ U, ∀ v ∈ U,
    Relation.ReflTransGen (fun a b => a ∈ U ∧ b ∈ U ∧ ∃ e, G.src e = a ∧ G.tgt e = b) u v

/-- An edge multiset `F : E → ℕ` (multiplicities) is Eulerian: `|δ⁺_F(v)| = |δ⁻_F(v)|` for every
vertex `v` (Def. 2.1, p. 7). -/
def IsEulerian (G : Graph V E) (F : E → ℕ) : Prop :=
  ∀ v : V, ∑ e ∈ outE G {v}, F e = ∑ e ∈ inE G {v}, F e

/-- `V(F)`: the vertices incident to an edge of positive multiplicity in `F`. -/
def vertsOf (G : Graph V E) (F : E → ℕ) : Finset V :=
  Finset.univ.filter (fun v => ∃ e, 0 < F e ∧ (G.src e = v ∨ G.tgt e = v))

/-- `a` and `b` are joined by an edge of `F` (in either direction): adjacency in the undirected graph
underlying `(V(F), F)`. -/
def adjF (G : Graph V E) (F : E → ℕ) (a b : V) : Prop :=
  ∃ e, 0 < F e ∧ ((G.src e = a ∧ G.tgt e = b) ∨ (G.src e = b ∧ G.tgt e = a))

/-- A subtour (Def. 2.1, p. 7): an Eulerian edge multiset `F` such that `(V(F), F)` is connected.
`F = 0` (the empty multiset) is a subtour. -/
def IsSubtour (G : Graph V E) (F : E → ℕ) : Prop :=
  IsEulerian G F ∧
    ∀ u ∈ vertsOf G F, ∀ v ∈ vertsOf G F, Relation.ReflTransGen (adjF G F) u v

/-- A tour (Def. 2.1, p. 7): a subtour `F` with `V(F) = V`. -/
def IsTour (G : Graph V E) (F : E → ℕ) : Prop :=
  IsSubtour G F ∧ vertsOf G F = Finset.univ

open Classical in
/-- The vertex set of the connected component of `(V(F), F)` containing `v` (a "subtour in `F`",
§2, p. 7). -/
noncomputable def comp (G : Graph V E) (F : E → ℕ) (v : V) : Finset V :=
  (vertsOf G F).filter (fun u => Relation.ReflTransGen (adjF G F) v u)

/-- The part of the multiset `F` on edges whose tail lies in `C`; for a component `C` of `(V(F), F)`
this is the subtour of `F` spanned by `C`. -/
def restrictTo (G : Graph V E) (F : E → ℕ) (C : Finset V) : E → ℕ :=
  fun e => if G.src e ∈ C then F e else 0

/-- Feasibility for the asymmetric Held–Karp relaxation LP(G, w) (§2.1, p. 7):
`x ≥ 0`, `x(δ⁺(v)) = x(δ⁻(v))` for every vertex `v`, and `x(δ(S)) ≥ 2` for every `∅ ≠ S ⊊ V`.
The constraints do not involve `w`, so this is also feasibility for LP(G, 0). -/
def IsHeldKarpFeasible (G : Graph V E) (x : E → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧
    (∀ v : V, ∑ e ∈ outE G {v}, x e = ∑ e ∈ inE G {v}, x e) ∧
    ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 2 ≤ ∑ e ∈ bdE G S, x e

/-- The proper nonempty vertex subsets `∅ ≠ S ⊊ V`, the index set of the dual variables `y_S`. -/
def properSets (V : Type) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.filter (fun S : Finset V => S.Nonempty ∧ S ≠ Finset.univ)

open Classical in
/-- Feasibility for DUAL(G, w) (§2.1, p. 8), with vertex potentials `a` (the page's `α`):
`y_S ≥ 0` for `∅ ≠ S ⊊ V`, and `∑_{S : e ∈ δ(S)} y_S + a(u) − a(v) ≤ w(e)` for every edge `e = (u, v)`. -/
def IsDualFeasible (G : Graph V E) (w : E → ℝ) (a : V → ℝ) (y : Finset V → ℝ) : Prop :=
  (∀ S ∈ properSets V, 0 ≤ y S) ∧
    ∀ e, (∑ S ∈ (properSets V).filter (fun S => e ∈ bdE G S), y S) + a (G.src e) - a (G.tgt e) ≤ w e

/-- The objective of DUAL(G, w): `∑_{∅ ≠ S ⊊ V} 2 y_S`. -/
def dualObj (y : Finset V → ℝ) : ℝ :=
  2 * ∑ S ∈ properSets V, y S

/-- A family of vertex subsets is laminar: any two members are nested or disjoint (§2.1, p. 8). -/
def IsLaminar (L : Finset (Finset V)) : Prop :=
  ∀ A ∈ L, ∀ B ∈ L, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

end ConstATSP.Gap


