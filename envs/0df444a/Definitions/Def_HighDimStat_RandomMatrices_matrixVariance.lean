-- Prove2me | Definitions.Def_HighDimStat_RandomMatrices_matrixVariance
-- name    : HighDimStat_RandomMatrices_matrixVariance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:18:22.21599+00:00
-- url     : https://prove2.me/theorems/bc1d714e-4ed0-48c6-bd61-f2c226d06171
-- title:
--   The matrix variance var(Q) = E[Q^2] - (E[Q])^2
-- statement:
--   The **matrix variance** of a random matrix $Q$,
--
--   $$
--   \mathrm{var}(Q) \;:=\; \mathbb E[Q^2] - (\mathbb E[Q])^2,
--   $$
--
--   a positive semidefinite matrix (Exercise 6.6), used to state both the Bernstein condition for
--   matrices (Definition 6.10) and the matrix Bernstein bound (Theorem 6.17).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 169 (PDF p. 189)

import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_matrixExpectation

open MeasureTheory

namespace HighDimStat.RandomMatrices

/-- **var(Q) := E[Q²] - (E[Q])²**, Wainwright, *High-Dimensional Statistics* (2019), p. 169. The
matrix variance of a random matrix `Q`, a positive semidefinite matrix (Exercise 6.6). -/
noncomputable def matrixVariance {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (Q : Ω → Matrix (Fin d) (Fin d) ℝ) (Prob : Measure Ω) : Matrix (Fin d) (Fin d) ℝ :=
  matrixExpectation (fun ω => Q ω ^ 2) Prob - (matrixExpectation Q Prob) ^ 2

end HighDimStat.RandomMatrices


