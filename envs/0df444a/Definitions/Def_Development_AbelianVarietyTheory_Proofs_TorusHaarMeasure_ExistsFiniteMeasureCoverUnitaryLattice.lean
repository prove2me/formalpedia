-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteMeasureCoverUnitaryLattice
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteMeasureCoverUnitaryLattice
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:11:53.715616+00:00
-- url     : https://prove2.me/theorems/644b40bc-2ff2-45dc-9bcb-729920b033ec
-- title:
--   Exists Finite Measure Cover Unitary Lattice
-- statement:
--   Definitions and structural lemmas for Exists Finite Measure Cover Unitary Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteMeasureCoverUnitaryLattice.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteMeasureCoverOfDriftFunction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CompactSpaceRealUnitaryGroupOfDefiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDriftFunctionRealUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GamDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsStabiliserImageSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CompactModLatticeStabiliserOfLeFirstMinimumStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.FiniteCovolume
end GlobalTheory.FiniteCovolume


