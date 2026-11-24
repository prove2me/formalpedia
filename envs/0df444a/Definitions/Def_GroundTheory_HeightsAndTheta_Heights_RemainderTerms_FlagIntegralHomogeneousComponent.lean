-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralHomogeneousComponent
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralHomogeneousComponent
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:59:48.557846+00:00
-- url     : https://prove2.me/theorems/388597b6-9175-497d-819b-3589ea58430a
-- title:
--   Flag Integral Homogeneous Component
-- statement:
--   Definitions and structural lemmas for Flag Integral Homogeneous Component, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralHomogeneousComponent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestPolynomialHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PVandermondeOfHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
def SmallBlockTermBound.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock), 1 ≤ f → 1 ≤ r → 1 ≤ a → r ≤ a →
    ∀ Q : ℕ → Fin f → RootRing f (r + a),
      IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) Q →
      ∀ k : ℕ, 2 ≤ k → k ≤ r + a → ∀ τ τ' : Fin f,
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ')| ≤
          ((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ)
namespace TermBoundEq
end TermBoundEq
open TermBoundEq
end
end GroundTheory.Heights₂.Heights.RestTerms


