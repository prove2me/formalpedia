-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsInvDerivDecay
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsInvDerivDecay
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:40.262019+00:00
-- url     : https://prove2.me/theorems/04f9fe2b-ca06-4f17-bd45-99ad4d2d9da0
-- title:
--   Statements Inv Deriv Decay
-- statement:
--   Definitions and structural lemmas for Statements Inv Deriv Decay, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/StatementsInvDerivDecay.lean

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
def InvDerivDecay.Statement : Prop :=
  ∀ (v G : ℂ → ℝ) (ρ R : ℝ), 0 < ρ → ContDiffOn ℝ 2 G (Metric.ball 0 ρ) →
    (∀ y : ℂ, R < ‖y‖ → v y = G y⁻¹) →
    ∃ C R₀ : ℝ, ∀ y : ℂ, R₀ < ‖y‖ →
      ‖fderiv ℝ v y‖ ≤ C / ‖y‖ ^ 2 ∧ ‖iteratedFDeriv ℝ 2 v y‖ ≤ C / ‖y‖ ^ 3
end GroundTheory.Heights₂.Heights.LowerBoundFree


