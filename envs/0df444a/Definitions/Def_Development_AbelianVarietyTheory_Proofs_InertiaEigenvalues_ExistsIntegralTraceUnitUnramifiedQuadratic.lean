-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnitUnramifiedQuadratic
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnitUnramifiedQuadratic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:29.590146+00:00
-- url     : https://prove2.me/theorems/f7a5806c-27f9-44d4-9f48-ea4f93cfe0f8
-- title:
--   Exists Integral Trace Unit Unramified Quadratic
-- statement:
--   Definitions and structural lemmas for Exists Integral Trace Unit Unramified Quadratic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralTraceUnitUnramifiedQuadratic.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.TraceUnit
section Ultra
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Ultra
end GlobalTheory.TraceUnit


