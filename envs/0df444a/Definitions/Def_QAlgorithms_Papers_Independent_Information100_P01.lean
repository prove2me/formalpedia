-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P01
-- name    : QAlgorithms_Papers_Independent_Information100_P01
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:24:07.601549+00:00
-- url     : https://prove2.me/theorems/dc64e01e-4f73-46f6-879e-d89e206fcbb1
-- title:
--   Definitions for On the coincidence of discrete and continuous definitions of Entanglement of Formation
-- statement:
--   The objects the formalized statements of *On the coincidence of discrete and continuous definitions of Entanglement of Formation* (arXiv:2610.18816) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsTraceOneOperator`: arxiv-2610.18816v1, PDF pp.3,13: a state, using the positive-operator criterion that its diagonal sum in a complete orthonormal basis is one. For a positive bounded operator this is exactly positive trace class with trace one. The ENNReal sum detects divergent diagonals rather than assigning them a real junk value. This predicate supplies no topology; it is used only for the range remark.
-- source:
--   On the coincidence of discrete and continuous definitions of Entanglement of Formation, arXiv:2610.18816v1, https://arxiv.org/abs/2610.18816v1

import Mathlib

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P01

/-- arxiv-2610.18816v1, PDF pp.3,13: a state, using the positive-operator
criterion that its diagonal sum in a complete orthonormal basis is one.
For a positive bounded operator this is exactly positive trace class with trace one.
The ENNReal sum detects divergent diagonals rather than assigning them a real junk value.
This predicate supplies no topology; it is used only for the range remark. -/
def IsTraceOneOperator {H I : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Countable I]
    (b : HilbertBasis I ℂ H) (rho : H →L[ℂ] H) : Prop :=
  rho.IsPositive ∧
    (∑' i, ENNReal.ofReal (inner ℂ (b i) (rho (b i))).re) = 1

/-- The zero operator is excluded, including on the zero Hilbert space. -/
example {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Countable I] (b : HilbertBasis I ℂ H) :
    ¬ IsTraceOneOperator b (0 : H →L[ℂ] H) := by
  simp [IsTraceOneOperator]

end QAlgorithms.Papers.Independent.Information100.P01


