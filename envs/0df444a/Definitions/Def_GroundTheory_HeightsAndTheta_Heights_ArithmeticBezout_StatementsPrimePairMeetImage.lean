-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimePairMeetImage
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimePairMeetImage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:49.464399+00:00
-- url     : https://prove2.me/theorems/6cc769cf-1079-4c7d-a633-2ad44042f3e0
-- title:
--   Statements Prime Pair Meet Image
-- statement:
--   Definitions and structural lemmas for Statements Prime Pair Meet Image, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsPrimePairMeetImage.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
def PrimePairMeetImage.Statement : Prop :=
  ∀ (n d : ℕ) (Q Q' : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ),
    Q.IsPrime → Q'.IsPrime → Q ≠ Q' →
    (∀ y : Fin d → ℂ, (ComplexSets.fibre Q A y).Finite) →
    (∀ y : Fin d → ℂ, (ComplexSets.fibre Q' A y).Finite) →
      ∃ e : MvPolynomial (Fin d) ℂ, e ≠ 0 ∧
        ∀ x ∈ ComplexSets.zeroSet Q ∩ ComplexSets.zeroSet Q', eval (A.mulVec x) e = 0
end GroundTheory.Heights₂.Heights


