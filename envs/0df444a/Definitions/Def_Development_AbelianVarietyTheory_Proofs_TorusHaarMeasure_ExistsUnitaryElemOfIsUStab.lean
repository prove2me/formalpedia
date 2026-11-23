-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsUnitaryElemOfIsUStab
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsUnitaryElemOfIsUStab
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:18.340802+00:00
-- url     : https://prove2.me/theorems/afafe84d-9612-4974-9c8c-04b1922ee3af
-- title:
--   Exists Unitary Elem Of Is UStab
-- statement:
--   Definitions and structural lemmas for Exists Unitary Elem Of Is UStab, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsUnitaryElemOfIsUStab.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FinMuOfFiniteCovolume
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
namespace GlobalTheory.FiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.FiniteCovolume


