-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaIntegral
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:16.582981+00:00
-- url     : https://prove2.me/theorems/b33a3b68-5803-473a-98f2-c6251579763c
-- title:
--   Statements Graph Area Integral
-- statement:
--   Definitions and structural lemmas for Statements Graph Area Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsGraphAreaIntegral.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
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
open scoped ENNReal
noncomputable section
def GraphAreaIntegral.Statement : Prop :=
  ∀ (d m n : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m) (Ω : Set (EuclideanSpace ℂ (Fin d)))
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)),
    IsOpen Ω → DifferentiableOn ℂ F Ω → ∀ A ⊆ Ω, MeasurableSet A →
    ∀ h : EuclideanSpace ℂ (Fin n) → ℝ≥0∞,
      ∫⁻ y in graphPt e F '' A, h y ∂(μH[((2 * d : ℕ) : ℝ)]) =
        ∫⁻ x in A, h (graphPt e F x) * ENNReal.ofReal (areaJacobian
          (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)))
          ∂(μH[((2 * d : ℕ) : ℝ)])
end
end GroundTheory.Heights₂.Heights


