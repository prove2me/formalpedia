-- Prove2me | Definitions.Def_HighDimStat_RandomMatrices_matrixExpectation
-- name    : HighDimStat_RandomMatrices_matrixExpectation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:03:32.324547+00:00
-- url     : https://prove2.me/theorems/182cff65-bc91-48c1-98d8-b629c7ca0f86
-- title:
--   The entrywise expectation of a random matrix
-- statement:
--   The **entrywise expectation** of a random matrix $Q$, $\mathbb E[Q] := (\mathbb E[Q_{ij}])_{ij}$,
--   used throughout Section 6.4.2 to define the matrix moment generating function, matrix
--   variance, and Bernstein condition.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 169 (PDF p. 189), Section 6.4.2

import Mathlib

open MeasureTheory

namespace HighDimStat.RandomMatrices

/-- The entrywise expectation of a random matrix, `E[Q] := (E[Q_{ij}])_{ij}`, used throughout
Wainwright, *High-Dimensional Statistics* (2019), Section 6.4.2, to define the matrix moment
generating function, matrix variance, and Bernstein condition. -/
noncomputable def matrixExpectation {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (Q : Ω → Matrix (Fin d) (Fin d) ℝ) (Prob : Measure Ω) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∫ ω, Q ω i j ∂Prob

end HighDimStat.RandomMatrices


