-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionComponents
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:37.272243+00:00
-- url     : https://prove2.me/theorems/8b6b99f7-274e-4d37-8e11-57be192e0efb
-- title:
--   Statements Section Components
-- statement:
--   Definitions and structural lemmas for Statements Section Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsSectionComponents.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionCycleReduced
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
def SectionComponents.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (J : Ideal (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin n) F),
    (∀ P ∈ J.minimalPrimes, ∀ Q ∈ J.minimalPrimes,
      ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ Q)) →
    (∀ P ∈ J.minimalPrimes, f ∉ P) →
    ∀ P ∈ J.minimalPrimes, ∀ W : Ideal (MvPolynomial (Fin n) F),
      W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ↔ W ∈ (J ⊔ Ideal.span {f}).minimalPrimes ∧ P ≤ W
end GroundTheory.Heights₂.Heights


