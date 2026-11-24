-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicDerivNeZero
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicDerivNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:45.713287+00:00
-- url     : https://prove2.me/theorems/fbc918fd-95cd-4825-b561-332ea15c6ed7
-- title:
--   St Injective Holomorphic Deriv Ne Zero
-- statement:
--   Definitions and structural lemmas for St Injective Holomorphic Deriv Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StInjectiveHolomorphicDerivNeZero.lean

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
namespace GroundTheory.Heights₂.Heights
noncomputable section
def InjectiveHolomorphicDerivNeZero.Statement : Prop :=
  ∀ (D : Set ℂ) (f : ℂ → ℂ), IsOpen D → DifferentiableOn ℂ f D → Set.InjOn f D → ∀ a ∈ D, deriv f a ≠ 0
end
end GroundTheory.Heights₂.Heights


