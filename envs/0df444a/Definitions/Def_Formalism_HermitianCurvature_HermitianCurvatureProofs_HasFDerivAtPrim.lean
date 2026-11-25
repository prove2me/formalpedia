-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtPrim
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtPrim
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:25.071996+00:00
-- url     : https://prove2.me/theorems/422a527f-77c2-4030-91b7-e1971ac5b19f
-- title:
--   Has FDeriv At Prim
-- statement:
--   Definitions and structural lemmas for Has FDeriv At Prim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtPrim.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtTMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory intervalIntegral Metric
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}
def seg (w₀ x : ℂ) (t : ℝ) : ℂ := w₀ + (t : ℂ) * (x - w₀)
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann


