-- Prove2me | Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
-- name    : D1Bound5_OrdinaryLog10_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:23:26.050036+00:00
-- url     : https://prove2.me/theorems/2e3a6267-0007-42d1-b30b-3bab6bbb068b
-- title:
--   Ordinary Log10
-- statement:
--   Defines the real logarithm to base ten by log₁₀(x) = log(x)/log(10). The named objects in this bundle include `ordinaryLog10`.
-- source:
--   D1Bound5/OrdinaryLog10.lean, lines 5-5, SHA-256 09aeaea7ebd8948074c88ecfb8ed793209871b3b024d7443a02f1048da4ea91c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

section
namespace D1Bound5

noncomputable def ordinaryLog10 (x : ℝ) : ℝ := Real.log x/Real.log 10





















end D1Bound5
end


