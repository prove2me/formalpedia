-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationPolynomialContour
-- name    : OAI_NumberTheory_DirichletL_ContinuationPolynomialContour
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:34:36.525411+00:00
-- url     : https://prove2.me/theorems/53f4d76a-9891-43e5-9d4d-19759ff4d994
-- title:
--   Continuation Polynomial Contour
-- statement:
--   Definitions and structural lemmas for Continuation Polynomial Contour, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ContinuationPolynomialContour.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationContour
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
set_option autoImplicit false
namespace OAI
noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
namespace SevenEighths.Continuation
def polynomialGaussian (n : ℕ) (y : ℝ) : ℝ :=
  (1+|y|^n)*Real.exp (-(y^2))
end SevenEighths.Continuation
end
end OAI


