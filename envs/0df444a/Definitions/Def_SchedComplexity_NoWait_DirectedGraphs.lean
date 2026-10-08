-- Prove2me | Definitions.Def_SchedComplexity_NoWait_DirectedGraphs
-- name    : SchedComplexity_NoWait_DirectedGraphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:49:35.002697+00:00
-- url     : https://prove2.me/theorems/a56ea114-4bfc-44d1-9dd5-d991c5fe74bf
-- title:
--   Directed Hamilton paths and circuits (Theorem 2(c),(d)) and the DIRECTED HAMILTON PATH language
-- statement:
--   A **directed graph** $G=(V,A)$ on the vertex set $V=\{0,\dots,n-1\}$ is given by its arc relation: $(u,v)\in A$ or not, for every ordered pair of vertices (loops $(v,v)$ allowed but irrelevant for paths).
--
--   1. A **Hamilton path** of $G$ (Brucker, Lenstra & Rinnooy Kan, Theorem 2(d): "a directed path passing through each vertex exactly once") is an ordering $\sigma(0),\sigma(1),\dots,\sigma(n-1)$ of all vertices, each exactly once, such that
--   $$(\sigma(i),\sigma(i+1))\in A\qquad (0\le i<n-1).$$
--   2. A **Hamilton circuit** (Theorem 2(c): "a directed cycle passing through each vertex exactly once") is such an ordering for which, in addition, the closing arc $(\sigma(n-1),\sigma(0))$ is in $A$.
--   3. The language **DIRECTED HAMILTON PATH** consists of the codes of the directed graphs that have a Hamilton path. The code of $G$ lists the number $n$ followed by the adjacency matrix row by row (entry $1$ for an arc, $0$ otherwise, diagonal included), every number written in binary.
--
--   DIRECTED HAMILTON PATH is the source problem of the reductions of Theorem 5; DIRECTED HAMILTON CIRCUIT is the problem it is reduced from in Theorem 2(d).
--
--   **Formalization Note** Vertices are $0$-based (`Fin n`) and the arc relation is a Boolean matrix. The orderings are bijections of `Fin n`. The paper is silent on tiny graphs; under this reading a graph with $n=0$ or $n=1$ vertices always has a Hamilton path, and a one-vertex graph has a Hamilton circuit iff it has a loop (the closing arc $(\sigma(0),\sigma(0))$). The alphabet `BSym` and binary code `encNats` are reused from the published `ProjSchedTW.Complexity.Encoding`.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 14, Theorem 2(c),(d)

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace SchedComplexity.NoWait

open ProjSchedTW.Complexity (BSym encNats)

/-- A Hamilton path of the directed graph on the vertex set `Fin n` with arc relation `adj`
(`adj u v = true` iff `(u, v)` is an arc): an ordering `σ 0, σ 1, …, σ (n-1)` of all vertices,
each vertex exactly once (`σ` is a bijection of `Fin n`), such that every two consecutive
vertices are joined by an arc `(σ i, σ (i+1))` (Theorem 2(d), p. 14: "a directed path passing
through each vertex exactly once"). Loops `adj v v` play no role. For `n = 0` and `n = 1` every
graph has a Hamilton path (the empty path, the one-vertex path). -/
def HasHamiltonPath {n : ℕ} (adj : Fin n → Fin n → Bool) : Prop :=
  ∃ σ : Fin n ≃ Fin n, ∀ (i : Fin n) (h : i.val + 1 < n), adj (σ i) (σ ⟨i.val + 1, h⟩) = true

/-- A Hamilton circuit of the directed graph on `Fin n` with arc relation `adj`: a cyclic
ordering `σ 0, …, σ (n-1)` of all vertices with arcs `(σ i, σ (i+1))` for `i < n-1` and the
closing arc `(σ (n-1), σ 0)` (Theorem 2(c), p. 14: "a directed cycle passing through each vertex
exactly once"). `finRotate n` sends `i` to `i + 1 mod n`. For `n = 1` the closing arc is a loop
`(v, v)`, so a one-vertex graph has a Hamilton circuit iff it has a loop; for `n = 0` the
condition is vacuous. -/
def HasHamiltonCircuit {n : ℕ} (adj : Fin n → Fin n → Bool) : Prop :=
  ∃ σ : Fin n ≃ Fin n, ∀ i : Fin n, adj (σ i) (σ (finRotate n i)) = true

/-- The code of a directed graph on `Fin n`: the list of natural numbers `n`, followed by the
adjacency matrix row by row (entry `1` for an arc, `0` otherwise, diagonal included), written
in binary with `encNats`. The code determines `n` and `adj`. -/
def dhpCode {n : ℕ} (adj : Fin n → Fin n → Bool) : List BSym :=
  encNats (n :: (List.ofFn fun u : Fin n => List.ofFn fun v : Fin n =>
    if adj u v then 1 else 0).flatten)

/-- DIRECTED HAMILTON PATH (Theorem 2(d), p. 14) as a language: the codes `dhpCode adj` of the
directed graphs that have a Hamilton path. -/
def dhpLang : CookPvsNP.Lang BSym :=
  { w | ∃ (n : ℕ) (adj : Fin n → Fin n → Bool), HasHamiltonPath adj ∧ w = dhpCode adj }

end SchedComplexity.NoWait


