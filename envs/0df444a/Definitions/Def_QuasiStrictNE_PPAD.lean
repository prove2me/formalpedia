-- Prove2me | Definitions.Def_QuasiStrictNE_PPAD
-- name    : QuasiStrictNE_PPAD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:24.152869+00:00
-- url     : https://prove2.me/theorems/c3341cc4-a639-45be-8be8-16926bb7965e
-- title:
--   The complexity class PPAD
-- statement:
--   A search problem $Q$ (a validity predicate and an answer relation on bit strings) belongs to **PPAD** when
--
--   1. $Q$ is **total**: every valid instance has at least one answer, and
--   2. $Q$ reduces to End-of-Line by a polynomial-time search reduction: polynomial-time maps $f$ and $g$ such that for every valid instance $I$ of $Q$, $f(I)$ is a valid End-of-Line instance and, for every solution $z$ of $f(I)$, $g(I,z)$ is an answer of $Q$ on $I$.
--
--   This is the definition of the paper (p.8): "The class PPAD consists of total search problems reducible to End-of-Line".
--
--   **Formalization Note** Search problems are the public `TetrisHard.Rows.SearchProblem` and reductions the public `CardinalMatching.SearchReduces` (Cook's Turing machines for polynomial time). Totality carries no bound on answer lengths, as on p.8.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §2, p.8

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_QuasiStrictNE_EndOfLine

namespace QuasiStrictNE

/-- **The class PPAD** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict
Equilibria*, arXiv:2611.06350, §2, p.8: "The class PPAD consists of total search problems reducible
to End-of-Line").

A search problem `Q` is in PPAD iff it is **total** (every valid instance has at least one answer)
and it reduces to `EndOfLine` by a polynomial-time search reduction (p.8: "polynomial-time
computable maps f and g such that, for every instance I of the source problem and every solution z
of the target instance f(I), the output g(I, z) is a solution of I").

**Formalization Note** Search problems are the public `TetrisHard.Rows.SearchProblem` (a validity
predicate and an answer relation on bit strings) and reductions the public
`CardinalMatching.SearchReduces`, which is exactly the p.8 definition. "Total" carries no bound on
the length of answers, as on p.8. -/
def PPAD : Set TetrisHard.Rows.SearchProblem :=
  {Q | (∀ s, Q.valid s → ∃ t, Q.answer s t) ∧ CardinalMatching.SearchReduces Q EndOfLine}

end QuasiStrictNE


