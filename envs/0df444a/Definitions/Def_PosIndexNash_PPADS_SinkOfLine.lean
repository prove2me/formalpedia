-- Prove2me | Definitions.Def_PosIndexNash_PPADS_SinkOfLine
-- name    : PosIndexNash_PPADS_SinkOfLine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:31:49.771742+00:00
-- url     : https://prove2.me/theorems/13d9238d-411e-478d-8b8f-c6a5953c9f64
-- title:
--   Normalized Sink-of-Line (Definition 2.4)
-- statement:
--   An instance of **normalized Sink-of-Line** consists of two Boolean circuits $S, P : \{0,1\}^n \to \{0,1\}^n$ satisfying
--   $$P(0^n) = 0^n \ne S(0^n) \qquad\text{and}\qquad P(S(0^n)) = 0^n.$$
--   The goal is to find a string $z \in \{0,1\}^n$ with $P(S(z)) \ne z$. (There is a directed edge $z \to z'$ when $S(z) = z'$ and $P(z') = z$; a solution is a vertex without a valid outgoing edge.)
--
--   `IsSOLInstance S P` is the instance condition. `SinkOfLine` is the search problem whose valid instances are the codes $\mathrm{enc}(S)\,\mathrm{enc}(P)$ of such pairs and whose answers are strings $z$ of length $n$ with $P(S(z)) \ne z$.
--
--   **Formalization Note** Circuits are the public well-formed `ConstrSOSP.Circuit` (gates ∧, ∨, ¬) with their evaluation and their self-delimiting code `encCircuit`; $0^n$ is `List.replicate n false`. Unlike End-of-Line, other sources ($S(P(z)) \ne z$) are not answers, and the normalization $P(S(0^n)) = 0^n$ is part of validity.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 14, Definition 2.4

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_ConstrSOSP_Circuit
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_Circuit_eval
import Definitions.Def_ConstrSOSP_encCircuit

namespace PosIndexNash.PPADS

/-- **Normalized Sink-of-Line instance** (Kontogiannis, Panageas, Pollatos, Yan, *Finding a Positive
Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879, p. 14, Definition 2.4).

Two well-formed Boolean circuits `S, P : {0,1}ⁿ → {0,1}ⁿ` (same `n`) with
`P(0ⁿ) = 0ⁿ ≠ S(0ⁿ)` and `P(S(0ⁿ)) = 0ⁿ`.

**Formalization Note** Circuits are the public `ConstrSOSP.Circuit` with `Circuit.WF` and
`Circuit.eval`; `0ⁿ` is `List.replicate n false`. -/
def IsSOLInstance (S P : ConstrSOSP.Circuit) : Prop :=
  S.WF ∧ P.WF ∧ S.n = P.n ∧
    P.eval (List.replicate S.n false) = List.replicate S.n false ∧
    S.eval (List.replicate S.n false) ≠ List.replicate S.n false ∧
    P.eval (S.eval (List.replicate S.n false)) = List.replicate S.n false

/-- **The search problem (normalized) Sink-of-Line** (Kontogiannis, Panageas, Pollatos, Yan,
*Finding a Positive Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879, p. 14,
Definition 2.4: "The goal is to find a string z ∈ {0,1}ⁿ such that P(S(z)) ≠ z").

A valid instance is the code `encCircuit S ++ encCircuit P` of a normalized instance
(`IsSOLInstance S P`). An answer is a bit string `z` of length `n` with `P(S(z)) ≠ z`.

**Formalization Note** Unlike End-of-Line, other sources (`S(P(z)) ≠ z`) are not answers, and
the normalization `P(S(0ⁿ)) = 0ⁿ` is part of validity. Codes are the public self-delimiting
`ConstrSOSP.encCircuit`, so an instance string determines `S` and `P`. -/
def SinkOfLine : TetrisHard.Rows.SearchProblem where
  valid s := ∃ S P : ConstrSOSP.Circuit, IsSOLInstance S P ∧
    s = ConstrSOSP.encCircuit S ++ ConstrSOSP.encCircuit P
  answer s z := ∃ S P : ConstrSOSP.Circuit, IsSOLInstance S P ∧
    s = ConstrSOSP.encCircuit S ++ ConstrSOSP.encCircuit P ∧
    z.length = S.n ∧ P.eval (S.eval z) ≠ z

end PosIndexNash.PPADS


