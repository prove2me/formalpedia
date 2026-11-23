-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianHarmonicProductKernelContinuousBounded
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianHarmonicProductKernelContinuousBounded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:10:15.260882+00:00
-- url     : https://prove2.me/theorems/8782c623-f50f-45df-954a-8c82004e98b0
-- title:
--   Gaussian Harmonic Product Kernel Continuous Bounded
-- statement:
--   Definitions and structural lemmas for Gaussian Harmonic Product Kernel Continuous Bounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianHarmonicProductKernelContinuousBounded.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
noncomputable section
namespace GlobalTheory.HeckeTheta.GaussBound
open GlobalTheory.HeckeTheta
end GlobalTheory.HeckeTheta.GaussBound


