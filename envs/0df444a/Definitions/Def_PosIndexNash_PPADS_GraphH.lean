-- Prove2me | Definitions.Def_PosIndexNash_PPADS_GraphH
-- name    : PosIndexNash_PPADS_GraphH
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:31:33.501742+00:00
-- url     : https://prove2.me/theorems/404f6535-348f-4783-85ea-e82841b38d11
-- title:
--   The graph H of a Sink-of-Line instance, its sources and sinks ((Graph), p. 20)
-- statement:
--   For a normalized Sink-of-Line instance $S, P$, the graph $H$ on the vertex set $\{0,1\}^n$ keeps exactly the edges that are not self-loops:
--   $$x \longrightarrow S(x) \iff S(x) \ne x \ \text{ and }\ P(S(x)) = x.$$
--   Every vertex has indegree and outdegree at most one. A **source** is a vertex of indegree zero and outdegree one, a **sink** a vertex of indegree one and outdegree zero (isolated vertices are neither), and a **noncanonical source** is a source $u \ne 0^n$.
--
--   **Formalization Note** Vertices are bit strings of length $n$ (the paper identifies them with the integers $0, \dots, 2^n - 1$). `HEdge S P x x'` is the edge relation; `IsHSource`, `IsHSink`, `IsHNoncanonicalSource` are the three vertex classes.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 20, (Graph) and the paragraph after it

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit
import Definitions.Def_ConstrSOSP_Circuit_eval

namespace PosIndexNash.PPADS

/-- **The graph `H` of a Sink-of-Line instance** (Kontogiannis, Panageas, Pollatos, Yan, *Finding a
Positive Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879, p. 20, (Graph)).

On the vertex set `{0,1}ⁿ`, `H` keeps exactly the edges that are not self-loops:
`x → S(x)` iff `S(x) ≠ x` and `P(S(x)) = x`. `HEdge S P x x'` says that `x` is a vertex
(a bit string of length `n = S.n`) and `x → x'` is an edge of `H`.

**Formalization Note** Vertices are bit strings `List Bool` of length `S.n` (the paper identifies
them with the integers `0, …, 2ⁿ − 1`). -/
def HEdge (S P : ConstrSOSP.Circuit) (x x' : List Bool) : Prop :=
  x.length = S.n ∧ x' = S.eval x ∧ x' ≠ x ∧ P.eval x' = x

/-- **Source of `H`** (p. 20: "a source means a vertex of indegree zero and outdegree one"):
a vertex `u` of length `n` with an outgoing edge and no incoming edge. Every vertex of `H` has
indegree and outdegree at most one, so "outdegree one" is "some outgoing edge". -/
def IsHSource (S P : ConstrSOSP.Circuit) (u : List Bool) : Prop :=
  u.length = S.n ∧ (∃ v, HEdge S P u v) ∧ ¬ ∃ z, HEdge S P z u

/-- **Sink of `H`** (p. 20: "a sink means a vertex of indegree one and outdegree zero; isolated
vertices are neither"): a vertex `u` of length `n` with an incoming edge and no outgoing edge. -/
def IsHSink (S P : ConstrSOSP.Circuit) (u : List Bool) : Prop :=
  u.length = S.n ∧ (∃ z, HEdge S P z u) ∧ ¬ ∃ v, HEdge S P u v

/-- **Noncanonical source of `H`** (p. 20, p. 23: a source `u ≠ 0ⁿ`). -/
def IsHNoncanonicalSource (S P : ConstrSOSP.Circuit) (u : List Bool) : Prop :=
  IsHSource S P u ∧ u ≠ List.replicate S.n false

end PosIndexNash.PPADS


