-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumGaussianConvolutionSeriesTermIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumGaussianConvolutionSeriesTermIntegral
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T20:28:45.145178+00:00
-- url     : https://prove2.me/theorems/2ef2792d-80d3-4d09-9df9-d4ef69b72644
-- title:
--   Has Sum Gaussian Convolution Series Term Integral
-- statement:
--   Definitions and structural lemmas for Has Sum Gaussian Convolution Series Term Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumGaussianConvolutionSeriesTermIntegral.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
open GlobalTheory.ConvSeries
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
end GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
namespace GlobalTheory.ConvSeries
open GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
end GlobalTheory.ConvSeries


