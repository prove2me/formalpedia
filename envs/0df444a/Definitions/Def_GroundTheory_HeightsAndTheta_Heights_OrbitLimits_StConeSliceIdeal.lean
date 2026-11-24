-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeSliceIdeal
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeSliceIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:53.994721+00:00
-- url     : https://prove2.me/theorems/ff74c8c7-0e0b-4b28-8868-353b36fefcfe
-- title:
--   St Cone Slice Ideal
-- statement:
--   Definitions and structural lemmas for St Cone Slice Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StConeSliceIdeal.lean

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
def ConeSliceIdeal.Statement : Prop :=
  ∀ (n : ℕ) (C : Set (Fin n → ℂ)) (t : Fin n → ℂ) (V : Ideal (MvPolynomial (Fin n) ℂ)),
    (∀ c ∈ C, ∀ a : ℂ, a ≠ 0 → a • c ∈ C) → MvPolynomial.vanishingIdeal ℂ C ≤ V →
      MvPolynomial.vanishingIdeal ℂ {x | x ∈ C ∧ MvPolynomial.eval x (linForm t) = 1} ≤
        V ⊔ Ideal.span {linForm t - 1}
end GroundTheory.Heights₂.Heights


