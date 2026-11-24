-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StMonicRootGrowth
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StMonicRootGrowth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:41.729847+00:00
-- url     : https://prove2.me/theorems/62034e5c-071d-4f71-aff9-9d724b269fe5
-- title:
--   St Monic Root Growth
-- statement:
--   Definitions and structural lemmas for St Monic Root Growth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/StMonicRootGrowth.lean

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
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
def MonicRootGrowth.Statement : Prop :=
  ∀ (d : ℕ) (m : Polynomial (MvPolynomial (Fin d) ℂ)), m.Monic →
    ∃ (C : ℝ) (M : ℕ), ∀ (y : Fin d → ℂ) (τ : ℂ), (m.map (eval y)).IsRoot τ →
      ‖τ‖ ≤ C * (1 + ‖y‖) ^ M
end GroundTheory.Heights₂.Heights.HilbertSamuel


