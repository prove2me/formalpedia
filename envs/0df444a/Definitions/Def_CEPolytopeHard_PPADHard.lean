-- Prove2me | Definitions.Def_CEPolytopeHard_PPADHard
-- name    : CEPolytopeHard_PPADHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:41.244723+00:00
-- url     : https://prove2.me/theorems/5d085fc2-fbb7-41b6-8fcc-c4a120544c9e
-- title:
--   PPAD-hardness of a search problem
-- statement:
--   A search problem $S$ (a validity predicate and an answer relation on bit strings) is **PPAD-hard** if every problem $Q$ in PPAD reduces to it:
--   $$
--   \forall Q \in \mathrm{PPAD},\quad Q \le_p S .
--   $$
--   Here PPAD is the class of total search problems that reduce to End-of-Line, and $Q \le_p S$ is a polynomial-time search (Levin) reduction: a polynomial-time instance map $f$ and answer map $g$ such that every valid instance $s$ of $Q$ is sent to a valid instance $f(s)$ of $S$, and for **every** answer $t$ of $S$ on $f(s)$, $g(s, t)$ is an answer of $Q$ on $s$.
--
--   This is the hardness notion of Theorem 4 and of Assumption 2.2.
--
--   **Formalization Note** The paper uses "PPAD-hard" without defining it. PPAD is the published `QuasiStrictNE.PPAD`, reductions are the published `CardinalMatching.SearchReduces` on Cook's Turing machines, and search problems are the published `TetrisHard.Rows.SearchProblem`.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Theorem 4, p.6 and Assumption 2.2, p.13 (the notion; not defined in the paper)

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_QuasiStrictNE_PPAD

set_option autoImplicit false

namespace CEPolytopeHard

/-- **PPAD-hardness** of a search problem (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang,
*The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version
of November 2, 2026, sha256 6aec500a…7820; used in Theorem 4, p.6, and Assumption 2.2, p.13).
A search problem `S` is PPAD-hard when every problem of PPAD reduces to it by a polynomial-time
search reduction.

**Formalization Note** The paper does not define PPAD-hardness. PPAD is the public
`QuasiStrictNE.PPAD` (total search problems reducing to End-of-Line) and reductions are the public
`CardinalMatching.SearchReduces` (polynomial-time instance and answer maps on Cook's machines,
correct for every answer of the target). -/
def PPADHard (S : TetrisHard.Rows.SearchProblem) : Prop :=
  ∀ Q ∈ QuasiStrictNE.PPAD, CardinalMatching.SearchReduces Q S

end CEPolytopeHard


