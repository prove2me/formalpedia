-- Prove2me | Definitions.Def_QuasiStrictNE_QSNE
-- name    : QuasiStrictNE_QSNE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:06.739226+00:00
-- url     : https://prove2.me/theorems/641d036d-21be-4b1d-a17a-b03da8e4876a
-- title:
--   The search problem QSNE: compute an exact quasi-strict Nash equilibrium
-- statement:
--   **QSNE** is the search problem: given a rational bimatrix game $(A,B)\in\mathbb Q^{m\times n}\times\mathbb Q^{m\times n}$ with $m,n\ge 1$, find rational vectors $x\in\mathbb Q^m$, $y\in\mathbb Q^n$ such that $(x,y)$ is a quasi-strict Nash equilibrium of the game. An instance is the code of the game, an answer the code of $x$ followed by the code of $y$.
--
--   **Formalization Note** Answers are exact rational equilibria, without an approximation parameter. $m,n\ge 1$ because $\Delta_0$ is empty. Vectors are written with the public `CardinalMatching.encRatVec`.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Theorem 1, p.2; Definition 1, p.4

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_QuasiStrictNE_RatGame
import Definitions.Def_QuasiStrictNE_RatGame_enc
import Definitions.Def_QuasiStrictNE_IsQSNE

namespace QuasiStrictNE

/-- **The search problem of computing a quasi-strict Nash equilibrium of a bimatrix game** (Hansen
& Nie, *On Existence and Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350,
Theorem 1, p.2: "Computing a quasi-strict Nash equilibrium of a bimatrix game"; Definition 1, p.4).

An instance is the code of a rational bimatrix game `(A, B)` with `m, n ≥ 1` pure strategies. An
answer is the code `encRatVec m x ++ encRatVec n y` of a pair of rational vectors that is a
quasi-strict Nash equilibrium of the game (`IsQSNE`).

**Formalization Note** Equilibria are exact: no approximation parameter. `m, n ≥ 1` because the
simplex `Δ0` is empty (p.4: "For k ≥ 1, … ∆k"). Rational data are cast to `ℝ` for the equilibrium
condition. The answer code `CardinalMatching.encRatVec` is the public self-delimiting code of a
rational vector, and the game code is `RatGame.enc`, so instance and answer strings determine the
game and the strategy pair. -/
def QSNE : TetrisHard.Rows.SearchProblem where
  valid s := ∃ G : RatGame, 1 ≤ G.m ∧ 1 ≤ G.n ∧ s = G.enc
  answer s t := ∃ (G : RatGame) (x : Fin G.m → ℚ) (y : Fin G.n → ℚ), 1 ≤ G.m ∧ 1 ≤ G.n ∧
    s = G.enc ∧ t = CardinalMatching.encRatVec G.m x ++ CardinalMatching.encRatVec G.n y ∧
    IsQSNE (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) (fun i => (x i : ℝ)) (fun j => (y j : ℝ))

end QuasiStrictNE


