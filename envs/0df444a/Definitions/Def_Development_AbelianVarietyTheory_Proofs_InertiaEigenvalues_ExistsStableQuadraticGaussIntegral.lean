-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsStableQuadraticGaussIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsStableQuadraticGaussIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:32.549396+00:00
-- url     : https://prove2.me/theorems/215d8b58-9b50-4265-87e9-719210301125
-- title:
--   Exists Stable Quadratic Gauss Integral
-- statement:
--   Definitions and structural lemmas for Exists Stable Quadratic Gauss Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsStableQuadraticGaussIntegral.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilUnipotentTorusPreserveTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.WeilQuad.GaussStable
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
end GlobalTheory.JR.WeilQuad.GaussStable


