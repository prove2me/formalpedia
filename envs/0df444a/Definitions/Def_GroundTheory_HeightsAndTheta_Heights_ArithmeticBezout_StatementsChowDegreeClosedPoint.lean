-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowDegreeClosedPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowDegreeClosedPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:36:30.564284+00:00
-- url     : https://prove2.me/theorems/67de6975-eb2b-48e3-945d-4123cab45ad4
-- title:
--   Statements Chow Degree Closed Point
-- statement:
--   Definitions and structural lemmas for Statements Chow Degree Closed Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsChowDegreeClosedPoint.lean

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
namespace ObjectsChow
open MvPolynomial
def ChowDegreeClosedPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (i : Fin n),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((1 : ℕ) : WithBot ℕ∞) → X i ∉ I →
      chowDegree I 1 = Module.finrank F (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1}))
end ObjectsChow
end GroundTheory.Heights₂.Heights


