-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:01.540263+00:00
-- url     : https://prove2.me/theorems/097e6734-f8b0-4d02-b8cc-22131ff18a9e
-- title:
--   Frobenius Bound Of Mul Near One
-- statement:
--   Definitions and structural lemmas for Frobenius Bound Of Mul Near One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FrobeniusBoundOfMulNearOne.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Metric Kronecker
noncomputable section
namespace Formalism.REAL
abbrev MatrixCoordinates (n : ℕ) := Fin n → Fin n → ℂ
def matrixCoordinatesEquiv (n : ℕ) : MatrixCoordinates n ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := Matrix.ofLinearEquiv ℝ
def leftMulReal {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : MatrixCoordinates n →ₗ[ℝ] MatrixCoordinates n :=
  ((matrixCoordinatesEquiv n).symm : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] MatrixCoordinates n) ∘ₗ
    ((LinearMap.mulLeft ℂ g).restrictScalars ℝ) ∘ₗ
    ((matrixCoordinatesEquiv n : MatrixCoordinates n ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      MatrixCoordinates n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
section frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
end frob
section frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
end frob
end Formalism.REAL


