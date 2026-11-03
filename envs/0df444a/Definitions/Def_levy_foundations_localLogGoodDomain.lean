-- Prove2me | Definitions.Def_levy_foundations_localLogGoodDomain
-- name    : levy_foundations_localLogGoodDomain
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T20:46:06.545513+00:00
-- url     : https://prove2.me/theorems/ddfc9cf9-5e2b-40c4-8017-ee9185888fb1
-- title:
--   Slit-plane domain of a complex-valued function
-- statement:
--   The good domain of a function from any type E to the complex numbers is the preimage of the slit plane under that function.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L82

import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace LevyFoundations.LocalLog
/-- Points where the complex logarithm avoids its branch cut. -/
def goodDomain {E : Type*} (φ : E → ℂ) : Set E :=
  φ ⁻¹' Complex.slitPlane
end LevyFoundations.LocalLog


