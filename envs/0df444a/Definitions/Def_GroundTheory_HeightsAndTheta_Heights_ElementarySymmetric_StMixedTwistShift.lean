-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:16:04.874388+00:00
-- url     : https://prove2.me/theorems/8e972a2d-8f57-4ed1-aad2-3c1414fe7a0c
-- title:
--   St Mixed Twist Shift
-- statement:
--   Definitions and structural lemmas for St Mixed Twist Shift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StMixedTwistShift.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open Classical in

def MixedTwistShift.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (qq : Ideal (Poly k N)), qq.IsPrime → (∀ f ∈ qq, ∀ d : ℕ, homogeneousComponent d f ∈ qq) →
    primeOf (S := k) x ≤ qq → ringKrullDim (Poly k N ⧸ qq) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) →
    ∀ (L : Fin n → LineBundle k x) (M : LineBundle k x) (d : ℤ), ∀ᶠ c : ℕ in atTop,
      ∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
          restrLen qq (((tensorSub (fun i => (L i).toSubSystem) T).twist M.toSubSystem).twist
            (twistSys k x ((c : ℤ) + d))) =
        if IsSubvar x qq n then interNum qq (fun i => (L i).toSubSystem) else 0
end
end GroundTheory.Heights₂.Heights.Kleiman


