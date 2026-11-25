-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:37.502261+00:00
-- url     : https://prove2.me/theorems/aa285fb0-1e9f-473b-8bb7-2a647eff5cf3
-- title:
--   Statements Cycle Split Filt
-- statement:
--   Definitions and structural lemmas for Statements Cycle Split Filt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsCycleSplitFilt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
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

def CycleSplit.Filt.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ J : Ideal (Poly S N), (∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) →
    primeOf (S := S) x ≤ J → 𝔪.map (C : S →+* Poly S N) ≤ J →
    ∃ (n : ℕ) (pp : Fin n → Ideal (Poly S N)) (d : Fin n → ℤ),
      (∀ j, (pp j).IsPrime ∧ (∀ p ∈ pp j, ∀ e : ℕ, homogeneousComponent e p ∈ pp j) ∧ J ≤ pp j) ∧
      (∀ (G : Ideal (Poly S N)) [G.IsPrime], G ∈ J.minimalPrimes →
        (((Finset.univ.filter fun j => pp j = G).card : ℕ) : ℕ∞) = cutMult J G) ∧
      ∀ Q : LineBundle S x, ∀ᶠ c : ℕ in atTop,
        restrLen J (Q.twist (twistSys S x (c : ℤ))) =
          ∑ j, restrLen (pp j) (Q.twist (twistSys S x ((c : ℤ) + d j)))
end
end GroundTheory.Heights₂.Heights.Kleiman


