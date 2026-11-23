-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralMulNorm
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralMulNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:40.905652+00:00
-- url     : https://prove2.me/theorems/8bf8b749-d230-4acf-a388-a89e028a8950
-- title:
--   Stable Quadratic Gauss Integral Mul Norm
-- statement:
--   Definitions and structural lemmas for Stable Quadratic Gauss Integral Mul Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StableQuadraticGaussIntegralMulNorm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
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
open scoped Pointwise ENNReal NNReal
namespace GlobalTheory.JR.WeilQuad.GaussTrans
end GlobalTheory.JR.WeilQuad.GaussTrans


