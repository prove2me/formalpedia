-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierCompSmul
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierCompSmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:43.961216+00:00
-- url     : https://prove2.me/theorems/db288d2a-db12-452a-b505-eb28bd6b1d69
-- title:
--   Quadratic Weil Fourier Comp Smul
-- statement:
--   Definitions and structural lemmas for Quadratic Weil Fourier Comp Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFourierCompSmul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualMeasuresAndAbsKScale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped NNReal
noncomputable section
namespace GlobalTheory.JR.WeilQuad
end GlobalTheory.JR.WeilQuad


