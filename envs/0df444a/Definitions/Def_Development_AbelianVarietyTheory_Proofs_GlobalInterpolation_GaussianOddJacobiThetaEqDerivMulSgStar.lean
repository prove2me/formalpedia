-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_GaussianOddJacobiThetaEqDerivMulSgStar
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_GaussianOddJacobiThetaEqDerivMulSgStar
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:00.648099+00:00
-- url     : https://prove2.me/theorems/c956ad4f-39eb-4272-b2a4-e88a9e633965
-- title:
--   Gaussian Odd Jacobi Theta Eq Deriv Mul Sg Star
-- statement:
--   Definitions and structural lemmas for Gaussian Odd Jacobi Theta Eq Deriv Mul Sg Star, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/GaussianOddJacobiThetaEqDerivMulSgStar.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
namespace GlobalTheory.SgStarOddTheta
open Formalism.L2.Th1.F
def expOddTheta (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  cexp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z
end GlobalTheory.SgStarOddTheta


