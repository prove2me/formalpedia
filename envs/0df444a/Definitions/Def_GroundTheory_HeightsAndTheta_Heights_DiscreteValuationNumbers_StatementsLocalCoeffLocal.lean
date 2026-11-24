-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:19.12361+00:00
-- url     : https://prove2.me/theorems/87831680-db08-49c1-8696-a8f8a298249b
-- title:
--   Statements Local Coeff Local
-- statement:
--   Definitions and structural lemmas for Statements Local Coeff Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsLocalCoeffLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
universe u
section Lemmas
def LocCycleSpanMul.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (x y : A), x ≠ 0 → y ≠ 0 →
    ∀ W : Ideal A, locCycle (Ideal.span {x * y}) W =
      locCycle (Ideal.span {x}) W + locCycle (Ideal.span {y}) W
def LocCyclePos.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (J W : Ideal R), W ∈ J.minimalPrimes →
    0 < locCycle J W
def MinimalPrimesSpanSingleton.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (x : A), x ≠ 0 →
    ∀ W : Ideal A, W ∈ (Ideal.span {x}).minimalPrimes ↔ W.IsPrime ∧ W.height = 1 ∧ x ∈ W
def LocalDomainDimTwo.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    (∀ Q₁ Q₂ : Ideal A, Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ → Q₂ < IsLocalRing.maximalIdeal A →
      False) →
    (∃ Q : Ideal A, Q.IsPrime ∧ ⊥ < Q ∧ Q < IsLocalRing.maximalIdeal A) →
    ringKrullDim A = 2 ∧ (IsLocalRing.maximalIdeal A).height = 2 ∧
      ∀ Q : Ideal A, Q.IsPrime → ⊥ < Q → Q < IsLocalRing.maximalIdeal A → Q.height = 1
def DimTwoSumReading.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    ringKrullDim A = 2 → ∀ a b : A, a ≠ 0 →
    (∀ p : Ideal A, p.IsPrime → p.height = 1 → a ∈ p → b ∉ p) →
    ∃ n : ℕ, ∑ᶠ W : Ideal A, locCycle (Ideal.span {a}) W *
        locCycle (W ⊔ Ideal.span {b}) (IsLocalRing.maximalIdeal A) = n ∧
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal), ordLoc p a * ordMod p b = n
end Lemmas
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


