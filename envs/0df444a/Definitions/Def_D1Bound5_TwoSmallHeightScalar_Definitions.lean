-- Prove2me | Definitions.Def_D1Bound5_TwoSmallHeightScalar_Definitions
-- name    : D1Bound5_TwoSmallHeightScalar_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:51:02.284984+00:00
-- url     : https://prove2.me/theorems/6ee41791-f711-4f3c-b77b-f52898cace22
-- title:
--   Two Small Height Scalar
-- statement:
--   The common ordinary two-anchor envelope when both anchors have modulus below three. The named objects in this bundle include `twoSmallHeightEnvelope`.
-- source:
--   D1Bound5/TwoSmallHeightScalar.lean, lines 5-8, SHA-256 2fc4438e81abf1fb9766cd269fcc8b00c95036ba7e21a2aa00ca22bc65122f73. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

section
namespace D1Bound5

/-- The common ordinary two-anchor envelope when both anchors have
modulus below three. -/
noncomputable def twoSmallHeightEnvelope (x : ℝ) : ℝ :=
  7*x+212/5+(4047/25)/(x-4)













end D1Bound5
end


