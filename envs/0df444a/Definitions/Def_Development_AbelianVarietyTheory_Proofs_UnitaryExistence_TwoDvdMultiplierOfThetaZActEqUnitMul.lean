-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TwoDvdMultiplierOfThetaZActEqUnitMul
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TwoDvdMultiplierOfThetaZActEqUnitMul
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:39:30.896809+00:00
-- url     : https://prove2.me/theorems/0e8b1837-401c-4bde-b4c9-34af8f0e55aa
-- title:
--   Two Dvd Multiplier Of Theta ZAct Eq Unit Mul
-- statement:
--   Definitions and structural lemmas for Two Dvd Multiplier Of Theta ZAct Eq Unit Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TwoDvdMultiplierOfThetaZActEqUnitMul.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory
section Transform
variable {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {τ : Matrix (Fin g) (Fin g) ℂ}
end Transform
end GlobalTheory


