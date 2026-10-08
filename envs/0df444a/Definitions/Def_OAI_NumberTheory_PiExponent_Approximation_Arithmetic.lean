-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic
-- name    : OAI_NumberTheory_PiExponent_Approximation_Arithmetic
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-08T13:23:37.155684+00:00
-- url     : https://prove2.me/theorems/6b1ef300-c311-4ddb-b85c-8d588035e79f
-- title:
--   Positive constant for least-common-multiple estimates
-- statement:
--   The real constant lcmConstant = log 4 + 4 is positive. The definition supplies an explicit positive coefficient for subsequent bounds on logarithms of least common multiples.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Arithmetic.lean#L13-L18

import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic







namespace OAI

namespace PiExponent.Arithmetic

noncomputable def lcmConstant : ℝ := Real.log 4 + 4

theorem lcmConstant_pos : 0 < lcmConstant := by
  have h : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  dsimp [lcmConstant]
  linarith





















































end PiExponent.Arithmetic

end OAI


