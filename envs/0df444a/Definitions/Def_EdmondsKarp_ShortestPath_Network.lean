-- Prove2me | Definitions.Def_EdmondsKarp_ShortestPath_Network
-- name    : EdmondsKarp_ShortestPath_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:09:06.168222+00:00
-- url     : https://prove2.me/theorems/2e90ba06-aab2-4d3a-852a-ae6d8453477e
-- title:
--   Network with source, sink, return arc $(t,s)$ and positive capacities; flows and maximum flows
-- statement:
--   Following Edmonds and Karp, a **network** $N$ consists of a finite set $V$ of nodes, a source $s$ and a sink $t$ with $s \neq t$, and a set of arcs, which are ordered pairs $(u,v)$ with $u \neq v$. Among the arcs is a special **return arc** $(t,s)$; the set of all other arcs is denoted $A$, so $(t,s) \notin A$. Because the arcs form a set of ordered pairs, there is at most one arc from a given node to another, while two opposite arcs $(u,v),(v,u) \in A$ are allowed. Every arc $(u,v) \in A$ carries a real **capacity** $c(u,v) > 0$.
--
--   A **flow** in $N$ is a function $f$ on the arcs of $N$ (including the return arc) such that $f(u,v) \ge 0$ on every arc, and
--
--   1. $f(u,v) \le c(u,v)$ for every $(u,v) \in A$;
--   2. for every node $u$,
--   $$\sum_{v} f(u,v) - \sum_{v} f(v,u) = 0,$$
--   where each sum runs over those $v$ for which the arc exists.
--
--   The value $f(t,s)$ on the return arc is the net amount of flow sent from $s$ to $t$ through the rest of the network. A flow $f$ is a **maximum flow** if $f(t,s) \ge g(t,s)$ for every flow $g$ in $N$.
--
--   These are the basic objects of the maximum network flow problem studied throughout the mission.
--
--   **Formalization Note** A network is a structure on a finite type `V` with decidable equality; `A` is a `Finset (V × V)` without loops and without `(t, s)`, and `c : V → V → ℝ` is positive on `A` (its values off `A` are irrelevant). A flow is a function `f : V → V → ℝ`; only its values on `A ∪ {(t,s)}` enter the conditions. A maximum flow is expressed as a predicate comparing return-arc values with every other flow, not as a supremum.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 249, §1.1 (definition of network, flow, maximum network flow problem)

import Mathlib

namespace EdmondsKarp.ShortestPath

/-- A network in the sense of Edmonds–Karp (1972), §1.1, p. 249: a finite node set `V`, a source `s`,
a sink `t`, the set `A` of all arcs *except* the return arc `(t, s)` (a set of ordered pairs, so at most
one arc from a node to another; no loops), and a capacity `c u v > 0` on every arc of `A`. Capacities are
real numbers. Values of `c` off `A` are irrelevant. -/
structure Network (V : Type) [Fintype V] [DecidableEq V] where
  s : V
  t : V
  source_ne_sink : s ≠ t
  A : Finset (V × V)
  no_loop : ∀ p ∈ A, p.1 ≠ p.2
  return_not_mem : (t, s) ∉ A
  c : V → V → ℝ
  cap_pos : ∀ p ∈ A, 0 < c p.1 p.2

variable {V : Type} [Fintype V] [DecidableEq V]

/-- All arcs of `N`: the arcs of `A` together with the return arc `(t, s)`. -/
def Network.arcs (N : Network V) : Finset (V × V) := insert (N.t, N.s) N.A

/-- A flow in `N` (§1.1, p. 249): a function `f u v`, meaningful on the arcs of `N` (values off the
arcs are ignored), which is nonnegative on every arc of `N` (including the return arc),
(i) at most the capacity on every arc of `A`, and (ii) conserves flow at every node `u`,
the sums running over the arcs of `N` leaving resp. entering `u`. -/
def IsFlow (N : Network V) (f : V → V → ℝ) : Prop :=
  (∀ u v, (u, v) ∈ N.arcs → 0 ≤ f u v) ∧
  (∀ u v, (u, v) ∈ N.A → f u v ≤ N.c u v) ∧
  (∀ u, (∑ v ∈ Finset.univ.filter (fun v => (u, v) ∈ N.arcs), f u v) -
      (∑ v ∈ Finset.univ.filter (fun v => (v, u) ∈ N.arcs), f v u) = 0)

/-- A maximum flow (§1.1, p. 249): a flow `f` whose return-arc value `f(t, s)` is at least `g(t, s)`
for every flow `g` in `N`. -/
def IsMaxFlow (N : Network V) (f : V → V → ℝ) : Prop :=
  IsFlow N f ∧ ∀ g : V → V → ℝ, IsFlow N g → g N.t N.s ≤ f N.t N.s

end EdmondsKarp.ShortestPath


