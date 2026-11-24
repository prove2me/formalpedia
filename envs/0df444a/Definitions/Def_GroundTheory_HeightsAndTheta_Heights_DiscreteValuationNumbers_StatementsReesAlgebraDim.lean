-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:52.683483+00:00
-- url     : https://prove2.me/theorems/fa867193-c81b-4058-9972-48a299eb0570
-- title:
--   Statements Rees Algebra Dim
-- statement:
--   Definitions and structural lemmas for Statements Rees Algebra Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsReesAlgebraDim.lean

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
universe u
def ReesAlgebraDim.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (I : Ideal A), I ≠ ⊥ →
    ∀ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) → ringKrullDim (reesAlgebra I) = ((n + 1 : ℕ) : WithBot ℕ∞)
end GroundTheory.Heights₂.Heights.NumbersDVR


