-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeVanishingHomog
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeVanishingHomog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:46.557133+00:00
-- url     : https://prove2.me/theorems/e1d15c3c-a6e4-4d2a-b5b1-75186893110f
-- title:
--   St Cone Vanishing Homog
-- statement:
--   Definitions and structural lemmas for St Cone Vanishing Homog, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StConeVanishingHomog.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
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
def ConeVanishingHomog.Statement : Prop :=
  ∀ (n : ℕ) (C : Set (Fin n → ℂ)), (∀ c ∈ C, ∀ a : ℂ, a ≠ 0 → a • c ∈ C) →
    IsHomogIdeal (MvPolynomial.vanishingIdeal ℂ C)
end GroundTheory.Heights₂.Heights


