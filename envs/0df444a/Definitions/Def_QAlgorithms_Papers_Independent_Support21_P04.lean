-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P04
-- name    : QAlgorithms_Papers_Independent_Support21_P04
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T03:28:41.751281+00:00
-- url     : https://prove2.me/theorems/e8175d39-7bc5-4a22-ae50-368177367213
-- title:
--   Definitions for A general proof of Landauer-Büttiker formula
-- statement:
--   The objects the formalized statements of *A general proof of Landauer-Büttiker formula* (arXiv:math-ph/0603030) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `transitionMatrix`: Nenciu, PDF p.5, equation (15): the two-channel transition matrix is constructed from the unitary scattering matrix by S = I - 2 pi i T.
-- source:
--   A general proof of Landauer-Büttiker formula, arXiv:math-ph/0603030v4, https://arxiv.org/abs/math-ph/0603030v4

import Mathlib

/-!
Nenciu, arXiv:math-ph/0603030v4, PDF p.5, equations (15)--(17).
Only the fixed-energy optical theorem is stated here. The six other inventoried
nodes are explicitly deferred in the unit's HARD.md and GAPS.json, including the
physical charge-conservation node: its trace-current model is not replaced by an
identity about arbitrary transmission coefficients. Compilation is pending the
batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P04

/-- Nenciu, PDF p.5, equation (15): the two-channel transition matrix is
constructed from the unitary scattering matrix by S = I - 2 pi i T. -/
def transitionMatrix (S : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (1 - (S : Matrix (Fin 2) (Fin 2) ℂ))

/-- The absence of scattering gives the zero transition matrix, including its
reflection entries; this pins the subtraction order in equation (15). -/
example : transitionMatrix (1 : Matrix.unitaryGroup (Fin 2) ℂ) = 0 := by
  simp [transitionMatrix]

end QAlgorithms.Papers.Independent.Support21.P04


