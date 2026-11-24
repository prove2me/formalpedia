-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:12.017937+00:00
-- url     : https://prove2.me/theorems/751ffa84-85f0-4037-91af-d875be1a583d
-- title:
--   Statements Kernel Proj Measurable
-- statement:
--   Definitions and structural lemmas for Statements Kernel Proj Measurable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsKernelProjMeasurable.lean

import Mathlib
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
open MeasureTheory
noncomputable section
def KernelProjMeasurable.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (n k : ℕ)
    (L : X → Matrix (Fin k) (Fin n) ℂ), Continuous L →
      Measurable fun x => (LinearMap.ker (Matrix.toEuclideanLin (L x))).starProjection
end
end GroundTheory.Heights₂.Heights


