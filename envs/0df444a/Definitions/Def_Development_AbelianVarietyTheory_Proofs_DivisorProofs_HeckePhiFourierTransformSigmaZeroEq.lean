-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformSigmaZeroEq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformSigmaZeroEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:30.175224+00:00
-- url     : https://prove2.me/theorems/08dd9a8a-9812-4c52-b42a-90f25363ac2e
-- title:
--   Hecke Phi Fourier Transform Sigma Zero Eq
-- statement:
--   Definitions and structural lemmas for Hecke Phi Fourier Transform Sigma Zero Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformSigmaZeroEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierLipschitzOneVariableKernelEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set
open scoped FourierTransform
namespace GlobalTheory.HeckeTwo
end GlobalTheory.HeckeTwo


