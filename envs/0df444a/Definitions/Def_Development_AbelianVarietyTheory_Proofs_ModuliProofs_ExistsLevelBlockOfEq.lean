-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:55.993058+00:00
-- url     : https://prove2.me/theorems/cb0068bd-df1e-4894-8cb3-ac1eb9a8e307
-- title:
--   Exists Level Block Of Eq
-- statement:
--   Definitions and structural lemmas for Exists Level Block Of Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLevelBlockOfEq.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.FrameFibre
variable {E : Type} [Field E] [NumberField E] {r : ℕ}
variable [IsCMField E]
end GlobalTheory.FrameFibre


