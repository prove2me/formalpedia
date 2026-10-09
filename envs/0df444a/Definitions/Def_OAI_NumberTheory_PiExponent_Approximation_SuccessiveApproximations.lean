-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations
-- name    : OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-09T09:49:18.752209+00:00
-- url     : https://prove2.me/theorems/74cfcd7f-9e25-450a-a16f-f6d00a7187e2
-- title:
--   Normalized logarithmic denominator weights
-- statement:
--   For any sequence q : ℕ → ℕ, normalizedLogWeights(q) is a function from ℕ to ℝ defined by normalizedLogWeights(q, 0) = 1 and normalizedLogWeights(q, n + 1) = Nat.ceil(log(q(n))), with the natural number ceiling coerced to ℝ. The zero-index value is exactly 1; every successor value is the ceiling of the logarithm of the preceding denominator. This is a definition only: it assumes no positivity condition on q and asserts no existence of an approximating sequence.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/SuccessiveApproximations.lean#L74-L76

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic


namespace OAI

namespace PiExponent







noncomputable def normalizedLogWeights (q : ℕ → ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (Nat.ceil (Real.log (q n)) : ℝ)











end PiExponent

end OAI


