-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PKernelProjMeasurable
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PKernelProjMeasurable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:56.987909+00:00
-- url     : https://prove2.me/theorems/ee78200d-ad41-4bda-9dd1-78427f263191
-- title:
--   PKernel Proj Measurable
-- statement:
--   Definitions and structural lemmas for PKernel Proj Measurable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PKernelProjMeasurable.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ContinuousLinearMap
noncomputable section
namespace KernelProjMeasurable
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
def shifted (A : E →L[ℂ] F) (ε : ℝ) : E →L[ℂ] E :=
  (ContinuousLinearMap.adjoint A) ∘L A + (ε : ℂ) • (1 : E →L[ℂ] E)
def resolvent (A : E →L[ℂ] F) (ε : ℝ) : E →L[ℂ] E :=
  (ε : ℂ) • Ring.inverse (shifted A ε)
end KernelProjMeasurable
end
end GroundTheory.Heights₂.Heights


