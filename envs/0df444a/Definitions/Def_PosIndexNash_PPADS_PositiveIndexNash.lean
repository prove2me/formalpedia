-- Prove2me | Definitions.Def_PosIndexNash_PPADS_PositiveIndexNash
-- name    : PosIndexNash_PPADS_PositiveIndexNash
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:32:37.062386+00:00
-- url     : https://prove2.me/theorems/2c73dca9-f74c-404d-98a7-9b8f1fddf8bd
-- title:
--   The promise search problem Positive-Index Nash (§1.2)
-- statement:
--   **Positive-Index Nash.** Input: two rational matrices $(A, B) \in \mathbb{Q}^{m\times n}\times\mathbb{Q}^{m\times n}$ defining a bimatrix game, under the promise that the game is nondegenerate. Output: an exact Nash equilibrium $(x, y)$ with $\mathrm{ind}_{A,B}(x, y) = +1$.
--
--   As a search problem on bit strings: a valid instance is the binary code of a rational game with $m, n \ge 1$ that is nondegenerate; an answer on it is the binary code of two rational vectors $x \in \mathbb{Q}^m$, $y \in \mathbb{Q}^n$ such that $(x, y)$ is a Nash equilibrium ($\mathrm{supp}(x) \subseteq BR_1(y)$, $\mathrm{supp}(y)\subseteq BR_2(x)$, $x\in\Delta_m$, $y \in \Delta_n$) and
--   $$\mathrm{ind}_{A,B}(x, y) = +1.$$
--
--   **Formalization Note** The nondegeneracy promise is part of validity: a search reduction is then required to be correct on nondegenerate inputs only, and a reduction *to* this problem must output nondegenerate games (p. 14). The answer relation repeats the validity of the instance. Codes are the public self-delimiting `QuasiStrictNE.RatGame.enc` and `CardinalMatching.encRatVec`; rational data are cast to $\mathbb{R}$ for the equilibrium and index conditions. $m, n \ge 1$ because $\Delta_0$ is empty.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 5, §1.2 (Positive-Index Nash); p. 12, Definitions 2.1–2.3; p. 14 (promise semantics)

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_QuasiStrictNE_RatGame
import Definitions.Def_QuasiStrictNE_RatGame_enc
import Definitions.Def_QuasiStrictNE_IsNE
import Definitions.Def_PosIndexNash_PPADS_Nondegenerate
import Definitions.Def_PosIndexNash_PPADS_ShapleyIndex

namespace PosIndexNash.PPADS

/-- **The promise search problem Positive-Index Nash** (Kontogiannis, Panageas, Pollatos, Yan,
*Finding a Positive Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879, §1.2, p. 5).

Input: two rational matrices `(A, B)` defining a bimatrix game, under the promise that the game is
nondegenerate. Output: an exact Nash equilibrium `(x, y)` with `ind_{A,B}(x, y) = +1`.

A valid instance is the code `G.enc` of a rational bimatrix game `G = (A, B)` with `m, n ≥ 1`
pure strategies that is nondegenerate (Definition 2.2). An answer on such an instance is the code
`encRatVec m x ++ encRatVec n y` of rational vectors `x, y` that form a Nash equilibrium
(Definition 2.1) with Shapley index `+1` (Definition 2.3).

**Formalization Note** The promise lives in `valid`: a polynomial-time search reduction
(`CardinalMatching.SearchReduces`) is then required to be correct on nondegenerate games only, and
a reduction *to* this problem must output nondegenerate games (p. 14). The answer relation repeats
the validity of the instance. Equilibria are exact rational vectors in binary (p. 12), cast to `ℝ`
for the equilibrium and index conditions. `m, n ≥ 1` because `Δ0` is empty. Codes are the public
self-delimiting `QuasiStrictNE.RatGame.enc` and `CardinalMatching.encRatVec`. -/
def PositiveIndexNash : TetrisHard.Rows.SearchProblem where
  valid s := ∃ G : QuasiStrictNE.RatGame, 1 ≤ G.m ∧ 1 ≤ G.n ∧ s = G.enc ∧
    Nondegenerate (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
  answer s t := ∃ (G : QuasiStrictNE.RatGame) (x : Fin G.m → ℚ) (y : Fin G.n → ℚ),
    1 ≤ G.m ∧ 1 ≤ G.n ∧ s = G.enc ∧
    Nondegenerate (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) ∧
    t = CardinalMatching.encRatVec G.m x ++ CardinalMatching.encRatVec G.n y ∧
    QuasiStrictNE.IsNE (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
      (fun i => (x i : ℝ)) (fun j => (y j : ℝ)) ∧
    shapleyIndex (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
      (fun i => (x i : ℝ)) (fun j => (y j : ℝ)) = 1

end PosIndexNash.PPADS


