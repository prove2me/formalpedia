-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusIntegral
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:29.004871+00:00
-- url     : https://prove2.me/theorems/1dc5067b-117a-4aaf-85ed-530c82c599bf
-- title:
--   Statements Torus Integral
-- statement:
--   Definitions and structural lemmas for Statements Torus Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsTorusIntegral.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory
open scoped ENNReal
noncomputable section
def TorusIntegralHomogeneous.Statement (κ : Type*) [Fintype κ] : Prop :=
  ∀ q : κ → ℝ, (∀ i, 0 < q i) → ∀ n : ℕ, ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧ ∀ t : ℝ, 0 < t →
    ∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2}.indicator
      (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b =
      C * ENNReal.ofReal (t ^ ((2 * n + 2) * Fintype.card κ))
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


