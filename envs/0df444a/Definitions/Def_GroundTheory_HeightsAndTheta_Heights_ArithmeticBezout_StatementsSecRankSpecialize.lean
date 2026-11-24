-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecRankSpecialize
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecRankSpecialize
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:25.574205+00:00
-- url     : https://prove2.me/theorems/9a41f335-a401-4a01-b9e3-4be208abbc63
-- title:
--   Statements Sec Rank Specialize
-- statement:
--   Definitions and structural lemmas for Statements Sec Rank Specialize, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsSecRankSpecialize.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
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
noncomputable section
def SecRankSpecialize.Statement : Prop :=
  ∀ (R K κ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field κ] [Algebra R κ] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Vertical.Par e n → R),
    Function.Surjective (algebraMap R κ) → Module.Finite R (Vertical.SecAlg Q y) →
      Module.finrank K
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y)) ≤
        Module.finrank κ
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y))
end
end GroundTheory.Heights₂.Heights


