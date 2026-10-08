-- Prove2me | Definitions.Def_Disjunctive_ExtendedFormulations_Basic_v2
-- name    : Disjunctive_ExtendedFormulations_Basic_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T22:00:28.16192+00:00
-- url     : https://prove2.me/theorems/740a00d3-210a-4a54-9804-fef7e7649aac
-- title:
--   Vocabulary of Chapter 5 (PMS, assignable and path-decomposable subgraph polytopes), with the corrected operator Γ*
-- statement:
--   Same definitions as `Disjunctive_ExtendedFormulations_Basic` (incidence vectors, $x(S)$, perfect matchings, the PMS polytope, $N(S)$, assignable vertex sets and the Assignable Subgraph Polytope, $\Gamma(S)$, $s$-$t$ path decompositions and the $s$-$t$ Path Decomposable Subgraph Polytope, acyclicity), except that the modified out-neighbourhood is now the book's
--
--   $$\Gamma^*(S) = \begin{cases} (\Gamma(S) \setminus \{t\}) \cup \Gamma(s) & t \in \Gamma(S),\\ \Gamma(S) & t \notin \Gamma(S),\end{cases}$$
--
--   whereas the retired module used $(\Gamma(S) \setminus \{t\}) \cup \{s\}$ (the node $s$ instead of its out-neighbourhood $\Gamma(s)$).
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §5.2.3, p. 75-76; operator also in Balas, Ann. Oper. Res. 140 (2005), Theorem 4.4

import Mathlib

namespace Disjunctive.ExtendedFormulations

/-- The incidence vector of a finite vertex set `W` (Balas §5.2.1, p. 74). -/
def IncidenceVec {V : Type*} [DecidableEq V] (W : Finset V) : V → ℝ :=
  fun i => if i ∈ W then 1 else 0

/-- `x(S) := Σ_{i∈S} x_i` (used throughout §5.2). -/
def xSum {V : Type*} (x : V → ℝ) (S : Finset V) : ℝ := ∑ i ∈ S, x i

/-- `G(W)` has a perfect matching: a fixed-point-free involution on `W` respecting adjacency
(Balas §5.2.1, p. 74). -/
def HasPerfectMatching {V : Type*} [DecidableEq V] (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∃ M : V → V, (∀ v ∈ W, M v ∈ W ∧ G.Adj v (M v)) ∧ ∀ v ∈ W, M (M v) = v

/-- The Perfectly Matchable Subgraph (PMS-) polytope: `conv(X)` where `X` is the set of incidence
vectors of vertex sets `W` such that `G(W)` has a perfect matching (Balas §5.2.1, p. 74). -/
def PMSPolytope {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Set (V → ℝ) :=
  convexHull ℝ {x : V → ℝ | ∃ W : Finset V, HasPerfectMatching G W ∧ x = IncidenceVec W}

/-- `N(S) := {j ∈ V \ S : (i,j) ∈ E for some i ∈ S}`, the (undirected) neighbor set of `S`,
excluding `S` itself (Balas §5.2.4, p. 76, `N(W)`; specializes to §5.2.1's `N(S)` for `S ⊆ V₁`
in a bipartite graph, where the exclusion is automatic). -/
def NeighborsF {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset V :=
  (Finset.univ.filter (fun j => ∃ i ∈ S, G.Adj i j)) \ S

/-- `G(W)` is assignable: it admits a cycle decomposition, i.e. a permutation of `W` respecting
arcs (Balas §5.2.2, p. 75-76). -/
def IsAssignable {V : Type*} [DecidableEq V] (A : V → V → Prop) (W : Finset V) : Prop :=
  ∃ σ : Equiv.Perm { v // v ∈ W }, ∀ v : { v // v ∈ W }, A v.1 (σ v).1

/-- The Assignable Subgraph Polytope of a digraph `(V,A)`: `conv` of incidence vectors of
assignable vertex sets (Balas §5.2.2, p. 75). -/
def AssignableSubgraphPolytope {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop) :
    Set (V → ℝ) :=
  convexHull ℝ {x : V → ℝ | ∃ W : Finset V, IsAssignable A W ∧ x = IncidenceVec W}

/-- `Γ(S) := {j ∈ V : (i,j) ∈ A for some i ∈ S}`, the digraph out-neighborhood of `S` (Balas
§5.2.2, p. 75). -/
def GammaOut {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop) [DecidableRel A]
    (S : Finset V) : Finset V :=
  Finset.univ.filter (fun j => ∃ i ∈ S, A i j)

/-- `Γ*(S)`, the modified out-neighborhood used for the `s`-`t` path-decomposable subgraph
polytope: `(Γ(S) \ {t}) ∪ Γ(s)` if `t ∈ Γ(S)`, and `Γ(S)` otherwise (Balas §5.2.3, p. 76; also
Balas, *Projection, lifting and extended formulation in integer and combinatorial optimization*,
Ann. Oper. Res. 140 (2005), Theorem 4.4). A path of the decomposition that leaves `S` towards `t`
is continued by a new path starting at `s`, i.e. at a node of `Γ(s)`; the earlier version of this
definition put the node `s` itself in place of `Γ(s)`, which makes the system of Theorem 5.3
cut off every path-decomposable set containing a predecessor of `t`. -/
def GammaStar {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop) [DecidableRel A]
    (s t : V) (S : Finset V) : Finset V :=
  if t ∈ GammaOut A S then (GammaOut A S \ {t}) ∪ GammaOut A {s} else GammaOut A S

/-- `G(W ∪ {s,t})` admits an `s`-`t` path decomposition: a set of arcs in which every interior
node of `W` has exactly one incoming and one outgoing chosen arc, and no chosen arc enters `s`
or leaves `t` — the standard degree-constrained encoding of a family of interior-node-disjoint
`s`-`t` paths covering `W` (Balas §5.2.3, p. 75-76). The empty family decomposes `W = ∅`; a
clause forcing a path out of `s` would make `∅` decomposable only when the arc `(s,t)` exists,
while the origin always satisfies the system of Theorem 5.3. -/
def IsPathDecomposable {V : Type*} [DecidableEq V] (A : V → V → Prop) (s t : V) (W : Finset V) :
    Prop :=
  ∃ F : Finset (V × V), (∀ e ∈ F, A e.1 e.2) ∧
    (∀ w ∈ W, (F.filter (fun e => e.1 = w)).card = 1) ∧
    (∀ w ∈ W, (F.filter (fun e => e.2 = w)).card = 1) ∧
    (F.filter (fun e => e.2 = s)).card = 0 ∧
    (F.filter (fun e => e.1 = t)).card = 0 ∧
    (∀ e ∈ F, e.1 = s ∨ e.1 ∈ W) ∧ (∀ e ∈ F, e.2 = t ∨ e.2 ∈ W)

/-- The `s`-`t` Path Decomposable Subgraph Polytope of an acyclic digraph: `conv` of incidence
vectors of path-decomposable vertex sets `W ⊆ V \ {s,t}` (Balas §5.2.3, p. 75). Its points carry
`x_s = x_t = 0`, which is the convention Theorem 5.3's system must also fix. -/
def PathDecomposableSubgraphPolytope {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop)
    (s t : V) : Set (V → ℝ) :=
  convexHull ℝ {x : V → ℝ | ∃ W : Finset V, s ∉ W ∧ t ∉ W ∧ IsPathDecomposable A s t W ∧
    x = IncidenceVec W}

/-- The digraph `(V, A)` is acyclic: no vertex reaches itself along a nonempty directed walk
(Balas §5.2.3, p. 75, "the acyclic digraph `G = (V, A)`"). -/
def IsAcyclicDigraph {V : Type*} (A : V → V → Prop) : Prop :=
  ∀ v : V, ¬ Relation.TransGen A v v

end Disjunctive.ExtendedFormulations


