-- Prove2me | Definitions.Def_QuasiStrictNE_EndOfLine
-- name    : QuasiStrictNE_EndOfLine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:11.937279+00:00
-- url     : https://prove2.me/theorems/7b8d1c36-15f2-4f2e-88cd-103f4906569d
-- title:
--   The search problem End-of-Line
-- statement:
--   **End-of-Line** is the search problem whose instances are pairs of well-formed Boolean circuits $S,P:\{0,1\}^n\to\{0,1\}^n$ with $n\ge 1$ such that
--   $$
--   P(0^n)=0^n\neq S(0^n),
--   $$
--   so the specified source $0^n$ has an outgoing edge and no incoming one. The answers to an instance are its solutions: bit strings $x$ of length $n$ with $P(S(x))\neq x$, or with $S(P(x))\neq x$ and $x\neq 0^n$ (another endpoint of a path).
--
--   End-of-Line is the problem that defines the class PPAD (p.8).
--
--   **Formalization Note** An instance is written as the code of $S$ followed by the code of $P$ (public self-delimiting `ConstrSOSP.encCircuit`), so the string determines the circuits. The circuits have no constant gates, which is why $n\ge 1$.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §2, p.8

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_ConstrSOSP_Circuit
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_Circuit_eval
import Definitions.Def_ConstrSOSP_encCircuit
import Definitions.Def_QuasiStrictNE_EOLSolution

namespace QuasiStrictNE

/-- **The search problem End-of-Line** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, §2, p.8: "Given an implicitly represented directed graph
with indegree and outdegree at most one and a specified source, find another endpoint [Pap94]").

An instance is the code `encCircuit S ++ encCircuit P` of two well-formed Boolean circuits
`S, P : {0,1}ⁿ → {0,1}ⁿ` with `n ≥ 1`, such that the specified source `0ⁿ` has an outgoing edge and
no incoming one: `P(0ⁿ) = 0ⁿ ≠ S(0ⁿ)`. The answers are the solutions `EOLSolution S P x`: bit strings
`x` of length `n` with `P(S(x)) ≠ x`, or with `S(P(x)) ≠ x` and `x ≠ 0ⁿ`.

**Formalization Note** The paper defines End-of-Line in words; this is the standard circuit form of
Daskalakis, Goldberg and Papadimitriou (edge `u → v` iff `S(u) = v` and `P(v) = u`). Circuits are
the public `ConstrSOSP.Circuit` (gates ∧, ∨, ¬; no constant gates, hence `n ≥ 1`) and their codes
the public self-delimiting `ConstrSOSP.encCircuit`, so an instance string determines `S` and `P`. -/
def EndOfLine : TetrisHard.Rows.SearchProblem where
  valid s := ∃ S P : ConstrSOSP.Circuit, S.WF ∧ P.WF ∧ S.n = P.n ∧ 1 ≤ S.n ∧
    P.eval (List.replicate S.n false) = List.replicate S.n false ∧
    S.eval (List.replicate S.n false) ≠ List.replicate S.n false ∧
    s = ConstrSOSP.encCircuit S ++ ConstrSOSP.encCircuit P
  answer s t := ∃ S P : ConstrSOSP.Circuit, S.WF ∧ P.WF ∧ S.n = P.n ∧ 1 ≤ S.n ∧
    P.eval (List.replicate S.n false) = List.replicate S.n false ∧
    S.eval (List.replicate S.n false) ≠ List.replicate S.n false ∧
    s = ConstrSOSP.encCircuit S ++ ConstrSOSP.encCircuit P ∧ EOLSolution S P t

end QuasiStrictNE


