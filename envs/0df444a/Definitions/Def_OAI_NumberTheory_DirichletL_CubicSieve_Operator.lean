-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_Operator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:11.511465+00:00
-- url     : https://prove2.me/theorems/28fefd54-8ccc-462b-a255-8bac6bc0a03c
-- title:
--   Operator
-- statement:
--   Definitions and structural lemmas for Operator, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/Operator.lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace OAI
namespace SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
def operator (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  A.toEuclideanLin.toContinuousLinearMap
def squaredNorm (A : Matrix m n ℂ) : ℝ := ‖operator A‖ ^ 2
def conjugateVector (x : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fun j => star (x j))
end
end SevenEighths.CubicSieve
end OAI


