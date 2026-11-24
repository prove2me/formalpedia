-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:10.914807+00:00
-- url     : https://prove2.me/theorems/60c0da3c-58e9-470b-bd18-7bc39773bed9
-- title:
--   St Punctured Exp Order
-- statement:
--   Definitions and structural lemmas for St Punctured Exp Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/StPuncturedExpOrder.lean

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
namespace GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology
noncomputable section
def PuncturedExpOrder.Statement : Prop :=
  ∀ (R : ℝ) (ψ : ℂ → ℂ) (k : ℤ) (M : ℝ), 0 < R → DifferentiableOn ℂ ψ (ball (0 : ℂ) R \ {0}) →
    (∀ x ∈ ball (0 : ℂ) R \ {0}, ‖Complex.exp (ψ x) * x ^ k‖ ≤ M) →
    0 ≤ k ∧ ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun x => Complex.exp (ψ x)) (𝓝[≠] 0) (𝓝 c)
end
end GroundTheory.Heights₂.Heights.Regular


