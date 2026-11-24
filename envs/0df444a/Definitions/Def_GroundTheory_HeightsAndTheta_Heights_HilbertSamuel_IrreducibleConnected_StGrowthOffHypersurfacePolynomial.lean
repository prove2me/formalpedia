-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StGrowthOffHypersurfacePolynomial
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StGrowthOffHypersurfacePolynomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:27.89686+00:00
-- url     : https://prove2.me/theorems/3ae303f1-f3e7-4813-a9b3-5b8689744aee
-- title:
--   St Growth Off Hypersurface Polynomial
-- statement:
--   Definitions and structural lemmas for St Growth Off Hypersurface Polynomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/StGrowthOffHypersurfacePolynomial.lean

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
def GrowthOffHypersurfacePolynomial.Statement : Prop :=
  ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ) (f : (Fin d → ℂ) → ℂ) (C : ℝ) (M : ℕ), Q ≠ 0 →
    DifferentiableOn ℂ f {y | eval y Q ≠ 0} →
    (∀ y : Fin d → ℂ, eval y Q ≠ 0 → ‖f y‖ ≤ C * (1 + ‖y‖) ^ M) →
    ∃ p : MvPolynomial (Fin d) ℂ, ∀ y : Fin d → ℂ, eval y Q ≠ 0 → f y = eval y p
end GroundTheory.Heights₂.Heights.HilbertSamuel


