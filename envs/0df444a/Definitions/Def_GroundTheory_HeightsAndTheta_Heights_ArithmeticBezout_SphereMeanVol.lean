-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:34.39455+00:00
-- url     : https://prove2.me/theorems/eb5a4c2e-ebcb-4b83-8446-aa84d339284e
-- title:
--   Sphere Mean Vol
-- statement:
--   Definitions and structural lemmas for Sphere Mean Vol, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
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
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
namespace SphereMean
section Linear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
end Linear
def sqNorm {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ j, ‖x j‖ ^ 2
def ballSet (n : ℕ) (s : ℝ) : Set (Fin n → ℂ) := {x | sqNorm x < s}
end SphereMean
end
end GroundTheory.Heights₂.Heights


