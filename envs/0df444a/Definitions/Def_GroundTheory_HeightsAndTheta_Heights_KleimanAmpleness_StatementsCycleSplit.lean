-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplit
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplit
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:57:19.991398+00:00
-- url     : https://prove2.me/theorems/32b70d64-fca8-44d7-afb6-fd1565119c6a
-- title:
--   Statements Cycle Split
-- statement:
--   Definitions and structural lemmas for Statements Cycle Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsCycleSplit.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreCycleDegree
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

def CycleSplit.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ J : Ideal (Poly S N), (∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) →
    primeOf (S := S) x ≤ J → 𝔪.map (C : S →+* Poly S N) ≤ J →
    (∀ G ∈ J.minimalPrimes, ringKrullDim (Poly S N ⧸ G) ≤ 2) →
    ∀ᶠ c : ℕ in atTop,
      interSum J ![M.toSubSystem] c =
        ∑ᶠ G : Ideal (Poly S N),
          if h : G ∈ J.minimalPrimes ∧ IsSubvar x G 1 then
            haveI : G.IsPrime := h.1.1.1
            ((cutMult J G).toNat : ℤ) * interNum G ![M.toSubSystem]
          else 0
end
end GroundTheory.Heights₂.Heights.Kleiman


