-- Prove2me | Definitions.Def_levy_foundations_localLogExponent
-- name    : levy_foundations_localLogExponent
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T20:46:15.389984+00:00
-- url     : https://prove2.me/theorems/72e923a5-407b-4c43-b749-3907bc9bf63b
-- title:
--   Local logarithmic exponent of a complex-valued function
-- statement:
--   Given any function φ from a type E to the complex numbers, its local logarithmic exponent at ξ is Complex.log (φ ξ).
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L93

import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace LevyFoundations.LocalLog
/-- Logarithmic exponent, continuous on the good domain under continuity. -/
noncomputable def localCharExponent {E : Type*}
    (φ : E → ℂ) (ξ : E) : ℂ :=
  Complex.log (φ ξ)
end LevyFoundations.LocalLog


