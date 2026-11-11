-- Prove2me | Definitions.Def_PosIndexNash_PPADS_PPADSClass
-- name    : PosIndexNash_PPADS_PPADSClass
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:33:00.215053+00:00
-- url     : https://prove2.me/theorems/aa4ac38a-21d1-4762-a91a-50e0c06a6f6a
-- title:
--   The class PPADS and PPADS-completeness (p. 14)
-- statement:
--   A **polynomial-time search reduction** from a search problem $Q$ to a search problem $R$ is a pair of polynomial-time maps $f$ (instances) and $g$ (answers) such that for every valid instance $s$ of $Q$, $f(s)$ is a valid instance of $R$, and for every answer $t$ of $R$ on $f(s)$, $g(s, t)$ is an answer of $Q$ on $s$.
--
--   The class **PPADS** consists of the search problems that reduce to (normalized) Sink-of-Line:
--   $$\mathrm{PPADS} := \{Q : Q \le_p \textsc{Sink-of-Line}\}.$$
--   A search problem $Q$ is **PPADS-complete** when $Q \in \mathrm{PPADS}$ and $R \le_p Q$ for every $R \in \mathrm{PPADS}$.
--
--   **Formalization Note** Reductions are the public `CardinalMatching.SearchReduces` (instance and answer maps computable in polynomial time on Cook's Turing machines; correctness on every valid instance and for every answer). No totality clause is imposed, as on p. 14. The Lean name `PPADSClass` avoids repeating the namespace `PosIndexNash.PPADS`.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 14 (the class PPADS); p. 5, Theorem 1.1 and p. 51, proof of Theorem 1.1 (completeness)

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_PosIndexNash_PPADS_SinkOfLine

namespace PosIndexNash.PPADS

/-- **The class PPADS** (Kontogiannis, Panageas, Pollatos, Yan, *Finding a Positive Index Nash
Equilibrium is PPADS-Complete*, arXiv:2609.23879, p. 14: "The class PPADS consists of the search
problems that admit a polynomial-time reduction to Sink-of-Line").

`PPADSClass` is the set of search problems `Q` with a polynomial-time search reduction from `Q` to the
normalized Sink-of-Line (Definition 2.4).

**Formalization Note** The Lean name `PPADSClass` avoids repeating the namespace
`PosIndexNash.PPADS`. Reductions are the public `CardinalMatching.SearchReduces` (instance and
answer maps computable in polynomial time on Cook's Turing machines, correct on every valid
input and for every answer). No totality clause is imposed, as on p. 14. -/
def PPADSClass : Set TetrisHard.Rows.SearchProblem :=
  {Q | CardinalMatching.SearchReduces Q SinkOfLine}

/-- **PPADS-completeness** (Kontogiannis, Panageas, Pollatos, Yan, *Finding a Positive Index Nash
Equilibrium is PPADS-Complete*, arXiv:2609.23879, p. 5, Theorem 1.1; p. 51, proof of
Theorem 1.1: membership and hardness).

`Q` is PPADS-complete iff `Q ∈ PPADS` and every problem of PPADS reduces to `Q`. -/
def PPADSComplete (Q : TetrisHard.Rows.SearchProblem) : Prop :=
  Q ∈ PPADSClass ∧ ∀ R ∈ PPADSClass, CardinalMatching.SearchReduces R Q

end PosIndexNash.PPADS


