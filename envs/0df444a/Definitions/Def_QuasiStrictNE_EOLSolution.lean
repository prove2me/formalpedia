-- Prove2me | Definitions.Def_QuasiStrictNE_EOLSolution
-- name    : QuasiStrictNE_EOLSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:05.460936+00:00
-- url     : https://prove2.me/theorems/5529370e-82bb-4e75-b04b-6551fda584c2
-- title:
--   Solution of an End-of-Line instance
-- statement:
--   Let $S,P:\{0,1\}^n\to\{0,1\}^n$ be Boolean circuits (successor and predecessor). They describe a directed graph on $\{0,1\}^n$ with an edge $u\to v$ exactly when $S(u)=v$ and $P(v)=u$; every vertex has indegree and outdegree at most one, and $0^n$ is the specified source. A bit string $x$ is a **solution** when it has length $n$ and is an endpoint other than the source:
--   $$
--   P(S(x))\neq x \qquad\text{or}\qquad \bigl(S(P(x))\neq x \ \text{ and }\ x\neq 0^n\bigr).
--   $$
--   The first case is a vertex without outgoing edge, the second a vertex other than $0^n$ without incoming edge.
--
--   **Formalization Note** This is the circuit form of End-of-Line due to Daskalakis, Goldberg and Papadimitriou; the paper describes the problem in words. Circuits are the public `ConstrSOSP.Circuit` with evaluation `Circuit.eval` on bit lists.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §2, p.8 (End-of-Line, after [Pap94])

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit
import Definitions.Def_ConstrSOSP_Circuit_eval

namespace QuasiStrictNE

/-- **A solution of an End-of-Line instance** (Hansen & Nie, *On Existence and Computational
Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, §2, p.8: "Given an implicitly represented
directed graph with indegree and outdegree at most one and a specified source, find another
endpoint [Pap94]").

The graph on `{0,1}ⁿ` is given by a successor circuit `S` and a predecessor circuit `P`; there is
an edge `u → v` iff `S(u) = v` and `P(v) = u`. The specified source is `0ⁿ`. A bit string `x` of
length `n` is a solution iff it is an endpoint other than the source:
`P(S(x)) ≠ x` (no outgoing edge: a sink, or the source when its successor does not point back), or
`S(P(x)) ≠ x` and `x ≠ 0ⁿ` (no incoming edge: another source).

**Formalization Note** This is the circuit form of Daskalakis, Goldberg and Papadimitriou; the paper
states the problem in words only. `n = S.n` is the number of input bits of `S`. -/
def EOLSolution (S P : ConstrSOSP.Circuit) (x : List Bool) : Prop :=
  x.length = S.n ∧
    (P.eval (S.eval x) ≠ x ∨ (S.eval (P.eval x) ≠ x ∧ x ≠ List.replicate S.n false))

end QuasiStrictNE


