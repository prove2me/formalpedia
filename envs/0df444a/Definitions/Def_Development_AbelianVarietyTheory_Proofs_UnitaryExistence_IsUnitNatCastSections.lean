-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsUnitNatCastSections
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsUnitNatCastSections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:28.666797+00:00
-- url     : https://prove2.me/theorems/3eb59957-f857-4035-bb85-0983700aea6b
-- title:
--   Is Unit Nat Cast Sections
-- statement:
--   Definitions and structural lemmas for Is Unit Nat Cast Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsUnitNatCastSections.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
namespace MulEtaleDvr
variable {S : Scheme.{0}}
end MulEtaleDvr
end GlobalTheory


