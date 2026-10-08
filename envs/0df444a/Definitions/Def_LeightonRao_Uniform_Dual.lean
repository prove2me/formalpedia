-- Prove2me | Definitions.Def_LeightonRao_Uniform_Dual
-- name    : LeightonRao_Uniform_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:54.989629+00:00
-- url     : https://prove2.me/theorems/38719a3a-7e93-4cee-81cd-f1c9a4a4e9dd
-- title:
--   §2.2, pp. 796–797 — distance functions, shortest-path distance, total weight W, distance constraint (5), radius, partition cross capacity
-- statement:
--   A **distance function** assigns a length $d(u,v)\ge0$ to every pair of nodes, symmetric in $u,v$; only its values on edges matter. The length of a walk in $G$ is the sum of the lengths of its edges, and the distance $d(u,v)$ between two nodes is the infimum of the lengths of the walks from $u$ to $v$. For a set $T$ of nodes, $d(T,u)=\min_{t\in T}d(t,u)$.
--
--   The **total weight** of $d$ is
--   $$W=\sum_{e\in E}C(e)\,d(e),$$
--   each undirected edge counted once. The **distance constraint** (5) of the dual of the UMFP is
--   $$\sum_{\{u,v\}}d(u,v)\ge1,$$
--   the sum over unordered pairs of nodes.
--
--   A set $S$ of nodes has **radius at most $\Delta$** if there is a centre $c\in S$ such that every $y\in S$ is reached from $c$ by a walk that stays inside $S$ and has length at most $\Delta$. For a partition of $V$ into components, the **cross capacity** is the total capacity of the edges joining nodes in different components.
--
--   These are the objects of Lemmas 3–6, which turn an optimal dual solution into a cut of small ratio cost.
--
--   **Formalization Note** Graph distances are infima over walks: they are $0$ for pairs with no connecting walk, which is why every statement that uses $d(u,v)$, $d(T,u)$ or (5) assumes the network is connected. $d(T,u)$ is meaningful for nonempty $T$ (for $T=\emptyset$ Lean returns $0$). The total weight and (5) are written as half of the sums over ordered pairs. The radius is intrinsic to the component (walks inside $S$), which is what the construction of Lemma 3 produces and what Lemma 6 uses; it is stronger than a bound on distances in $G$.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 796 (§2.2, Eqs. (4)–(5), total weight W), p. 797 (Lemma 3: radius, components), p. 799 (Lemma 5: d(T, u))

import Definitions.Def_LeightonRao_Uniform_Network

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A nonnegative symmetric edge-distance assignment. Values on nonedges are ignored. -/
def IsDistanceFunction (d : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ d u v) ∧ (∀ u v, d u v = d v u)

/-- Length of a graph walk in the assigned edge distances. -/
noncomputable def walkLen (N : Network V) (d : V → V → ℝ)
    {u v : V} (p : N.graph.Walk u v) : ℝ :=
  (p.darts.map (fun a => d a.fst a.snd)).sum

/-- Shortest path distance on the positive-capacity graph. The walk index is nonempty
under `IsConnectedNet N`; every theorem using it states that assumption. -/
noncomputable def dist (N : Network V) (d : V → V → ℝ) (u v : V) : ℝ :=
  ⨅ p : N.graph.Walk u v, walkLen N d p

/-- Distance `d(T, u)` from a vertex set to a vertex. Meaningful for nonempty `T`; for
`T = ∅` the infimum over the empty index is Lean's junk value `0`. -/
noncomputable def distFrom (N : Network V) (d : V → V → ℝ)
    (T : Finset V) (u : V) : ℝ :=
  ⨅ t : T, dist N d t u

/-- `W = ∑ C(e)d(e)`, counting every undirected edge once. -/
noncomputable def totalWeight (N : Network V) (d : V → V → ℝ) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, N.C u v * d u v

/-- Equation (5): the dual's sum is over unordered vertex pairs. -/
def SatisfiesDistanceConstraint (N : Network V) (d : V → V → ℝ) : Prop :=
  1 ≤ (1 / 2) * ∑ u, ∑ v, dist N d u v

/-- The radius bound is witnessed by walks lying entirely within the component. -/
def HasRadiusLE (N : Network V) (d : V → V → ℝ)
    (S : Finset V) (Δ : ℝ) : Prop :=
  ∃ c ∈ S, ∀ y ∈ S, ∃ p : N.graph.Walk c y,
    (∀ x ∈ p.support, x ∈ S) ∧ walkLen N d p ≤ Δ

/-- Capacity of the edges whose endpoints lie in different partition components. -/
noncomputable def crossCap (N : Network V)
    (P : Finpartition (Finset.univ : Finset V)) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, if P.part u = P.part v then 0 else N.C u v

end LeightonRao.Uniform


