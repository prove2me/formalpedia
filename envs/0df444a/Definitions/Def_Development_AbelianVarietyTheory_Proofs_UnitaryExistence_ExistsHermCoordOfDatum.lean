-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:08.661848+00:00
-- url     : https://prove2.me/theorems/781058a3-07fc-444c-966e-5c231bfa4fd5
-- title:
--   Exists Herm Coord Of Datum
-- statement:
--   Definitions and structural lemmas for Exists Herm Coord Of Datum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsHermCoordOfDatum.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.DatumCoord
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
end GlobalTheory.DatumCoord
namespace GlobalTheory
open DatumCoord
end GlobalTheory


