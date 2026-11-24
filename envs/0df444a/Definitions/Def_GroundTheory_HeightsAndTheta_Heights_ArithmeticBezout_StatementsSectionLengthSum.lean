-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionLengthSum
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionLengthSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:11.32333+00:00
-- url     : https://prove2.me/theorems/d48c17d5-7fce-45f0-ae7b-d6071c960a40
-- title:
--   Statements Section Length Sum
-- statement:
--   Definitions and structural lemmas for Statements Section Length Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsSectionLengthSum.lean

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
open Classical in

def SectionLengthSum.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J W : Ideal A) (f : A),
    J.IsRadical →
    (∀ P ∈ J.minimalPrimes, f ∉ P) →
    W ∈ (J ⊔ Ideal.span {f}).minimalPrimes →
    (∀ P ∈ J.minimalPrimes, P ≤ W → W ∈ (P ⊔ Ideal.span {f}).minimalPrimes) →
      localMult (J ⊔ Ideal.span {f}) W =
        ∑ P ∈ (J.finite_minimalPrimes_of_isNoetherianRing A).toFinset with P ≤ W,
          localMult (P ⊔ Ideal.span {f}) W
end GroundTheory.Heights₂.Heights


