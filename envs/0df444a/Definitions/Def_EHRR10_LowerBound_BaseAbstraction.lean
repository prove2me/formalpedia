-- Prove2me | Definitions.Def_EHRR10_LowerBound_BaseAbstraction
-- name    : EHRR10_LowerBound_BaseAbstraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:18:42.124617+00:00
-- url     : https://prove2.me/theorems/962dbc71-80d4-4020-bb0c-6e43818a785c
-- title:
--   Condition i) and the base abstraction 𝓑_{d,n}: graphs on d-subsets of [n] in which u and v are joined through vertices containing u ∩ v
-- statement:
--   Write $[n] = \{1,\dots,n\}$ and $\binom{[n]}{d}$ for the family of all $d$-element subsets of $[n]$ (the paper writes $[n]^d$). The base abstraction of Eisenbrand, Hähnle, Razborov and Rothvoß is given by a connected graph $G = (V, E)$ whose vertex set is a family $V \subseteq \binom{[n]}{d}$, subject to one connectivity condition:
--
--   **Condition i).** For each $u, v \in V$ there exists a path in $G$ connecting $u$ and $v$ whose intermediate vertices all contain $u \cap v$.
--
--   The class $\mathcal B_{d,n}$ is the set of all such graphs. The paper calls $d$ the **dimension** and $n$ the **number of facets** of the abstraction, and writes $D(d,n)$ for the largest diameter of a graph in $\mathcal B_{d,n}$.
--
--   This file provides two predicates, for a finite family $V$ of subsets of $[n]$ and a simple graph $G$ on $V$:
--
--   1. $\mathrm{CondI}(V, G)$: condition i), i.e. for all $u, v \in V$ there is a walk from $u$ to $v$ in $G$ every vertex $w$ of which satisfies $u \cap v \subseteq w$;
--   2. $\mathrm{InB}(d, n, V, G)$: $V$ is nonempty, every member of $V$ has exactly $d$ elements, and $\mathrm{CondI}(V, G)$ holds; that is, $G \in \mathcal B_{d,n}$.
--
--   The motivation is geometric: in a non-degenerate $d$-dimensional polyhedron with $n$ facets, each vertex is determined by the $d$ facets containing it, and two vertices can be joined without leaving the smallest face containing both, i.e. through vertices lying on every facet that contains both $u$ and $v$. Condition i) keeps only this feature. Every statement of this series of missions about $D(d,n)$ is phrased through these predicates.
--
--   **Formalization Note** $[n]$ is `Fin n` $=\{0,\dots,n-1\}$; the index base is immaterial. Vertices are the $d$-sets themselves (`V : Finset (Finset (Fin n))`, `G : SimpleGraph V`), so two distinct vertices always carry distinct sets. Condition i) is stated with walks and asks that *every* vertex of the walk contain $u \cap v$: a walk contains a path on a subset of its vertices, and the endpoints contain $u\cap v$ trivially, so this is the page's condition. Connectivity of $G$ follows from condition i); "connected" is encoded only by $V \neq \emptyset$. $D(d,n)$ is not defined as a number: statements about it are phrased through `SimpleGraph.dist` on a graph satisfying `InB`.
-- source:
--   Eisenbrand, Hähnle, Razborov, Rothvoß, Diameter of Polyhedra: Limits of Abstraction, Dagstuhl Seminar Proceedings 10211 (2010), http://drops.dagstuhl.de/opus/volltexte/2010/2724, p. 2, condition i), the definition of B_{d,n} and D(d,n), and footnote 1

import Mathlib

namespace EHRR10.LowerBound

/-- Condition i) of Eisenbrand–Hähnle–Razborov–Rothvoß (Dagstuhl 10211, 2010, p. 2): for each
`u, v ∈ V` there is a walk in `G` from `u` to `v` every vertex of which contains `u ∩ v`.
(A walk suffices: every walk contains a path on a subset of its vertices; the endpoints contain
`u ∩ v` trivially, so "every vertex" is the same as "every intermediate vertex".) -/
def CondI {n : ℕ} (V : Finset (Finset (Fin n))) (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ p : G.Walk u v, ∀ w ∈ p.support,
    (u : Finset (Fin n)) ∩ (v : Finset (Fin n)) ⊆ (w : Finset (Fin n))

/-- The base abstraction `𝓑_{d,n}`: a graph `G` on a nonempty family `V` of `d`-element subsets of
`[n]` (here `Fin n`) satisfying condition i). -/
def InB (d n : ℕ) (V : Finset (Finset (Fin n))) (G : SimpleGraph V) : Prop :=
  V.Nonempty ∧ (∀ v ∈ V, v.card = d) ∧ CondI V G

end EHRR10.LowerBound


