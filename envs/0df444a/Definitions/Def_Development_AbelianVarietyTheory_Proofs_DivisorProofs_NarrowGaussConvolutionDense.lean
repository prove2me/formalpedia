-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NarrowGaussConvolutionDense
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_NarrowGaussConvolutionDense
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T20:45:15.455514+00:00
-- url     : https://prove2.me/theorems/2f0f0fdd-c2d7-4289-a935-6bfa1b67182c
-- title:
--   Narrow Gauss Convolution Dense
-- statement:
--   Definitions and structural lemmas for Narrow Gauss Convolution Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NarrowGaussConvolutionDense.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemClosureWideGaussianMulSchwartzStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
namespace GlobalTheory.NarrowGauss
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
noncomputable def gauss (c : ℝ) (hc : 0 < c) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.smulOfNeZero ℝ E (Real.sqrt (c / Real.pi))
      (Real.sqrt_ne_zero'.2 (div_pos hc Real.pi_pos))).toContinuousLinearEquiv)
    (GroundTheory.Global.gaussianSchwartz E)
end GlobalTheory.NarrowGauss


