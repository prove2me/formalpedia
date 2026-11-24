-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsLaplacianDecayZero
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsLaplacianDecayZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:40.342929+00:00
-- url     : https://prove2.me/theorems/27adbfd0-0c84-4ca5-80b0-923573f49221
-- title:
--   Statements Laplacian Decay Zero
-- statement:
--   Definitions and structural lemmas for Statements Laplacian Decay Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/StatementsLaplacianDecayZero.lean

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
open InnerProductSpace Laplacian
def LaplacianDecayZero.Statement : Prop :=
  ∀ (v : ℂ → ℝ) (C R₀ : ℝ), ContDiff ℝ 2 v →
    (∀ y : ℂ, R₀ < ‖y‖ →
      ‖fderiv ℝ v y‖ ≤ C / ‖y‖ ^ 2 ∧ ‖iteratedFDeriv ℝ 2 v y‖ ≤ C / ‖y‖ ^ 3) →
    MeasureTheory.Integrable (Δ v) ∧ ∫ y, Δ v y = 0
def LaplacianDecayZero.bump : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
end GroundTheory.Heights₂.Heights.LowerBoundFree


