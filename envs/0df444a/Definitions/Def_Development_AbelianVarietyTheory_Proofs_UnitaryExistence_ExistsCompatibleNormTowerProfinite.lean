-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsCompatibleNormTowerProfinite
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsCompatibleNormTowerProfinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:34:17.423162+00:00
-- url     : https://prove2.me/theorems/cec742b6-157d-4bb5-8e6a-78bd32942f5f
-- title:
--   Exists Compatible Norm Tower Profinite
-- statement:
--   Definitions and structural lemmas for Exists Compatible Norm Tower Profinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsCompatibleNormTowerProfinite.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalfStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.NormTower
end GlobalTheory.NormTower


