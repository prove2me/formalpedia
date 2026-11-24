-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsLocalMultOrd
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsLocalMultOrd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:34.400833+00:00
-- url     : https://prove2.me/theorems/4a85116a-b180-4357-81e5-b736e4b10027
-- title:
--   Statements Local Mult Ord
-- statement:
--   Definitions and structural lemmas for Statements Local Mult Ord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsLocalMultOrd.lean

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
noncomputable section
def LocalMultOrd.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (I W : Ideal A) (x : A)
    [(W.map (Ideal.Quotient.mk I)).IsPrime], W ∈ (I ⊔ Ideal.span {x}).minimalPrimes →
      ((localMult (I ⊔ Ideal.span {x}) W : ℕ) : ℕ∞) =
        Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk I)))
          (algebraMap _ _ (Ideal.Quotient.mk I x))
section Inhabitants
open MvPolynomial
end Inhabitants
end
end GroundTheory.Heights₂.Heights


