-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootGridLower
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootGridLower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:27.080314+00:00
-- url     : https://prove2.me/theorems/bf7ccdab-e63b-4805-a5e6-bee7bea30635
-- title:
--   Statements Root Grid Lower
-- statement:
--   Definitions and structural lemmas for Statements Root Grid Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsRootGridLower.lean

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
def RootGridLower.Statement : Prop :=
  ∀ (e m : ℕ) (Q : MvPolynomial (Fin e) ℤ), Q ≠ 0 → (∀ i, Q.degreeOf i < m) →
    ∃ ζ : Fin e → ℂ, (∀ i, ζ i ^ m = 1) ∧ 1 ≤ ‖eval ζ (map (Int.castRingHom ℂ) Q)‖
end GroundTheory.Heights₂.Heights.HilbertSamuel


