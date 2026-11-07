-- Prove2me | Definitions.Def_QuasiStrictNE_FixSearch
-- name    : QuasiStrictNE_FixSearch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:17.420206+00:00
-- url     : https://prove2.me/theorems/39db5162-3a01-4cc4-a0a2-db4de1a13882
-- title:
--   The search problem of an exact rational fixed point
-- statement:
--   For a piecewise-linear fixed-point problem, the search problem **FixSearch** asks, for a valid instance $I$, for a rational point $x\in D_I$ with $F_I(x)=x$. Every exact rational fixed point is an answer.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Theorem 3, p.9

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_QuasiStrictNE_PLFPData
import Definitions.Def_QuasiStrictNE_PLFPData_D

namespace QuasiStrictNE

/-- **The search problem of an exact rational fixed point** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Theorem 3, p.9: "The search
problem of computing such an exact rational fixed point belongs to PPAD").

For a piecewise-linear fixed-point problem `Φ`, the valid instances are those of `Φ`, and an answer
to `I` is the code `encRatVec (dim I) x` of a rational point `x ∈ D_I` with `F_I(x) = x`.

**Formalization Note** Every exact rational fixed point is an answer; the polynomial bound on the
encoding length of some fixed point is the separate existence clause of `theorem_3`. -/
def FixSearch (Φ : PLFPData) : TetrisHard.Rows.SearchProblem where
  valid I := Φ.valid I
  answer I t := ∃ x : Fin (Φ.dim I) → ℚ, t = CardinalMatching.encRatVec (Φ.dim I) x ∧
    (fun i => (x i : ℝ)) ∈ Φ.D I ∧ Φ.F I (fun i => (x i : ℝ)) = fun i => (x i : ℝ)

end QuasiStrictNE


