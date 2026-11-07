-- Prove2me | Definitions.Def_QuasiStrictNE_PPADComplete
-- name    : QuasiStrictNE_PPADComplete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:40.032211+00:00
-- url     : https://prove2.me/theorems/8bb03f39-9562-4cec-a745-b9dfd8d356ed
-- title:
--   PPAD-completeness
-- statement:
--   A search problem $Q$ is **PPAD-complete** when $Q\in\mathrm{PPAD}$ (membership) and every problem $R\in\mathrm{PPAD}$ reduces to $Q$ by a polynomial-time search reduction (hardness).
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Theorem 1, p.2; §2, p.8

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_QuasiStrictNE_PPAD

namespace QuasiStrictNE

/-- **PPAD-completeness** (Hansen & Nie, *On Existence and Computational Complexity of Quasi-strict
Equilibria*, arXiv:2611.06350, Theorem 1, p.2; PPAD and search reductions as defined on p.8).

`Q` is PPAD-complete iff `Q ∈ PPAD` (membership) and every problem of PPAD reduces to `Q` by a
polynomial-time search reduction (hardness). -/
def PPADComplete (Q : TetrisHard.Rows.SearchProblem) : Prop :=
  Q ∈ PPAD ∧ ∀ R ∈ PPAD, CardinalMatching.SearchReduces R Q

end QuasiStrictNE


