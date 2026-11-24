-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:17.699845+00:00
-- url     : https://prove2.me/theorems/d7bf9f76-968b-4331-9277-cf5326e4764d
-- title:
--   PPointwise Lelong
-- statement:
--   Definitions and structural lemmas for PPointwise Lelong, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
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
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
namespace PointwiseLelong
variable {N : ℕ}
def radialMap (p z : Fin N → ℂ) : ℝ × (Fin N → ℂ) := (‖coordAlong p z‖, orthoDir p z)
def polarMap (p z : Fin N → ℂ) : ℝ × (ℝ × (Fin N → ℂ)) :=
  (Complex.arg (coordAlong p z), radialMap p z)
def polarIntegrand (Q : MvPolynomial (Fin N) ℂ) (p : Fin N → ℂ) (x : ℝ × (ℝ × (Fin N → ℂ))) : ℝ :=
  Real.log ‖eval (((x.2.1 : ℂ) * Complex.exp (x.1 * Complex.I)) • p +
    ((√(1 - x.2.1 ^ 2) : ℝ) : ℂ) • x.2.2) Q‖
end PointwiseLelong
end
end GroundTheory.Heights₂.Heights


