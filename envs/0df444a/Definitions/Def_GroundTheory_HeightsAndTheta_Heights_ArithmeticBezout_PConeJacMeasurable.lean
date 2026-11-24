-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeJacMeasurable
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeJacMeasurable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:45.518138+00:00
-- url     : https://prove2.me/theorems/4164957f-a484-487b-b94b-e927dc5b104a
-- title:
--   PCone Jac Measurable
-- statement:
--   Definitions and structural lemmas for PCone Jac Measurable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
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
open MvPolynomial MeasureTheory Module
noncomputable section
variable {n : ℕ}
def coneJacMat (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : Matrix (Fin k) (Fin n) ℂ :=
  Matrix.of (fun i j => eval (h.pointOf y) (pderiv j (g i))) * h.mat.transpose
def gramOp {m : ℕ} (π : Fin m → Fin n → ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (LinearMap.toContinuousLinearMap (linProjₗ π)).adjoint ∘L LinearMap.toContinuousLinearMap (linProjₗ π)
def compressDet {m : ℕ} (π : Fin m → Fin n → ℂ)
    (Q : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : ℝ :=
  Complex.re (Q ∘L gramOp π ∘L Q + (1 - Q)).det
end
end GroundTheory.Heights₂.Heights


