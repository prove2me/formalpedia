-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRatPrimeDense
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRatPrimeDense
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:40.278943+00:00
-- url     : https://prove2.me/theorems/e1d71799-0546-4712-92c0-395d99f19417
-- title:
--   Statements Rat Prime Dense
-- statement:
--   Definitions and structural lemmas for Statements Rat Prime Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsRatPrimeDense.lean

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
def RatPrimeDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℚ)) (f : MvPolynomial σ ℚ), P.IsPrime → f ∉ P →
    {z : σ → ℂ | ∀ g ∈ P, aeval z g = 0} ⊆
      closure {z : σ → ℂ | (∀ g ∈ P, aeval z g = 0) ∧ aeval z f ≠ 0}
end GroundTheory.Heights₂.Heights.HilbertSamuel


