-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StEntirePolynomialGrowth
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StEntirePolynomialGrowth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:53.980615+00:00
-- url     : https://prove2.me/theorems/f86f8654-5b53-47df-ae52-a6797c2e94a9
-- title:
--   St Entire Polynomial Growth
-- statement:
--   Definitions and structural lemmas for St Entire Polynomial Growth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/StEntirePolynomialGrowth.lean

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
def EntirePolynomialGrowth.Statement : Prop :=
  ∀ (d : ℕ) (f : (Fin d → ℂ) → ℂ) (C : ℝ) (M : ℕ), Differentiable ℂ f →
    (∀ y : Fin d → ℂ, ‖f y‖ ≤ C * (1 + ‖y‖) ^ M) →
    ∃ p : MvPolynomial (Fin d) ℂ, ∀ y : Fin d → ℂ, f y = eval y p
end GroundTheory.Heights₂.Heights.HilbertSamuel


