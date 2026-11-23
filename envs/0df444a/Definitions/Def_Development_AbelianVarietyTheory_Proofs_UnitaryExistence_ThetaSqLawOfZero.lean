-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaSqLawOfZero
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaSqLawOfZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:37.426618+00:00
-- url     : https://prove2.me/theorems/0c86554c-4480-485f-815e-3e5a85db7e5d
-- title:
--   Theta Sq Law Of Zero
-- statement:
--   Definitions and structural lemmas for Theta Sq Law Of Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaSqLawOfZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ThetaCharMult
variable {g : ℕ}
end GlobalTheory.ThetaCharMult


