-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:50.809409+00:00
-- url     : https://prove2.me/theorems/72677732-2b11-4150-9e26-dad0387bb0fe
-- title:
--   Log Int Sphere
-- statement:
--   Definitions and structural lemmas for Log Int Sphere, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
namespace HermNorm
variable {n : ℕ}
end HermNorm
namespace LogInt
variable {n k : ℕ}
def inGroup (i : Fin k) : Fin k × Fin n → Prop := fun ij => ij.1 = i
instance (i : Fin k) : DecidablePred (inGroup (n := n) i) := fun ij => by
  unfold inGroup; infer_instance
def normT (h : HermNorm n) (T : Finset (Fin k)) (u : Fin k × Fin n → ℂ) : Fin k × Fin n → ℂ :=
  fun ij => if ij.1 ∈ T then ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij else u ij
end LogInt
end
end GroundTheory.Heights₂.Heights


