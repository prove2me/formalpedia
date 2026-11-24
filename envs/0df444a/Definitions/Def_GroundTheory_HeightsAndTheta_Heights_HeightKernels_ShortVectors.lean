-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:53.732562+00:00
-- url     : https://prove2.me/theorems/ac846ee6-4320-4379-88bf-ebe059633730
-- title:
--   Short Vectors
-- statement:
--   Definitions and structural lemmas for Short Vectors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
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
open MeasureTheory Module Metric
noncomputable section
namespace KShort
def cube (n : ℕ) (c : ℝ) : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, |x i| < c}
end KShort
namespace KShort
variable {n : ℕ}
end KShort
namespace KShort
variable {n : ℕ}
end KShort
end
end GroundTheory.Heights₂.Heights


