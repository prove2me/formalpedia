-- Prove2me | Definitions.Def_QuasiStrictNE_Nash
-- name    : QuasiStrictNE_Nash
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:07.374994+00:00
-- url     : https://prove2.me/theorems/594bdda6-d380-48cd-8c45-55f77d890ee6
-- title:
--   The search problem Nash: compute an exact Nash equilibrium
-- statement:
--   **Nash** is the search problem: given a rational bimatrix game $(A,B)\in\mathbb Q^{m\times n}\times\mathbb Q^{m\times n}$ with $m,n\ge 1$, find rational vectors $x\in\mathbb Q^m$, $y\in\mathbb Q^n$ such that $(x,y)$ is a Nash equilibrium of the game. Instances and answers are coded as for QSNE.
--
--   **Formalization Note** Answers are exact rational equilibria.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §1, p.2; proof of Theorem 1, p.19 ([CDT09])

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_QuasiStrictNE_RatGame
import Definitions.Def_QuasiStrictNE_RatGame_enc
import Definitions.Def_QuasiStrictNE_IsNE

namespace QuasiStrictNE

/-- **The search problem of computing a Nash equilibrium of a bimatrix game** (Hansen & Nie, *On
Existence and Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, §1, p.2:
"computing a Nash equilibrium of bimatrix games"; proof of Theorem 1, p.19, "PPAD-completeness of
computing a bimatrix Nash equilibrium by [CDT09]"; Definition 1, p.4).

An instance is the code of a rational bimatrix game `(A, B)` with `m, n ≥ 1` pure strategies. An
answer is the code `encRatVec m x ++ encRatVec n y` of a pair of rational vectors that is a Nash
equilibrium of the game (`IsNE`).

**Formalization Note** Equilibria are exact: no approximation parameter. `m, n ≥ 1` because the
simplex `Δ0` is empty (p.4: "For k ≥ 1, … ∆k"). Rational data are cast to `ℝ` for the equilibrium
condition. The answer code `CardinalMatching.encRatVec` is the public self-delimiting code of a
rational vector, and the game code is `RatGame.enc`, so instance and answer strings determine the
game and the strategy pair. -/
def Nash : TetrisHard.Rows.SearchProblem where
  valid s := ∃ G : RatGame, 1 ≤ G.m ∧ 1 ≤ G.n ∧ s = G.enc
  answer s t := ∃ (G : RatGame) (x : Fin G.m → ℚ) (y : Fin G.n → ℚ), 1 ≤ G.m ∧ 1 ≤ G.n ∧
    s = G.enc ∧ t = CardinalMatching.encRatVec G.m x ++ CardinalMatching.encRatVec G.n y ∧
    IsNE (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) (fun i => (x i : ℝ)) (fun j => (y j : ℝ))

end QuasiStrictNE


