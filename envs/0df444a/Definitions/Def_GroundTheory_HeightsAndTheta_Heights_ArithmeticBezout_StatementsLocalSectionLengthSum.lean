-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLocalSectionLengthSum
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLocalSectionLengthSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:48.099961+00:00
-- url     : https://prove2.me/theorems/8cbb0651-2221-4102-b6c7-cb150fc1f72a
-- title:
--   Statements Local Section Length Sum
-- statement:
--   Definitions and structural lemmas for Statements Local Section Length Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsLocalSectionLengthSum.lean

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
def LocalSectionLengthSum.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (J : Ideal B) (f : B),
    J.IsRadical →
    (∀ P ∈ J.minimalPrimes, f ∉ P) →
    (∀ Q : Ideal B, Q.IsPrime → J ≤ Q → Q ∈ J.minimalPrimes ∨ Q = IsLocalRing.maximalIdeal B) →
      Module.length B (B ⧸ (J ⊔ Ideal.span {f})) =
        ∑ P ∈ (J.finite_minimalPrimes_of_isNoetherianRing B).toFinset,
          Module.length B (B ⧸ (P ⊔ Ideal.span {f}))
end GroundTheory.Heights₂.Heights


