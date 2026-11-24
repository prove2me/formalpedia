-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionCycleReduced
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionCycleReduced
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:57.02456+00:00
-- url     : https://prove2.me/theorems/28b25018-0db4-486f-a3a5-5c943f67e5ba
-- title:
--   Statements Section Cycle Reduced
-- statement:
--   Definitions and structural lemmas for Statements Section Cycle Reduced, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsSectionCycleReduced.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormSectionPerfect
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
open MvPolynomial
def SectionCycleReduced.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (J : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F),
    J.IsRadical →
    (∀ P ∈ J.minimalPrimes, ∀ Q ∈ J.minimalPrimes,
      ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ Q)) →
    (∀ P ∈ J.minimalPrimes, linForm u ∉ P) →
      fundCycle (J ⊔ Ideal.span {linForm u}) = ∑ P ∈ (fundCycle J).support, divCycle P u
end GroundTheory.Heights₂.Heights


