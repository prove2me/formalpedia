-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffRing
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:19.447475+00:00
-- url     : https://prove2.me/theorems/0720eea9-6b60-419e-8560-24981ec622f2
-- title:
--   Statements Local Coeff Ring
-- statement:
--   Definitions and structural lemmas for Statements Local Coeff Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsLocalCoeffRing.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocCycle
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
noncomputable section
universe u
section Defs
variable {R : Type*} [CommRing R]
abbrev localQuot (P U : Ideal R) [U.IsPrime] : Type _ :=
  Localization.AtPrime U ⧸ P.map (algebraMap R (Localization.AtPrime U))
def localQuotMap (P U : Ideal R) [U.IsPrime] : R →+* localQuot P U :=
  (Ideal.Quotient.mk _).comp (algebraMap R (Localization.AtPrime U))
end Defs
section Lemmas
def LocalQuotRing.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P.IsPrime → P ≤ U →
    IsDomain (localQuot P U) ∧ IsLocalRing (localQuot P U) ∧
      (∀ y : localQuot P U, IsUnit y ↔ y ∉ U.map (localQuotMap P U)) ∧
      ∀ x : R, localQuotMap P U x = 0 ↔ x ∈ P
def LocalQuotPrimes.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P ≤ U →
    (∀ W : Ideal R, W.IsPrime → P ≤ W → W ≤ U →
      (W.map (localQuotMap P U)).IsPrime ∧ (W.map (localQuotMap P U)).comap (localQuotMap P U) = W) ∧
    ∀ p : Ideal (localQuot P U), p.IsPrime →
      P ≤ p.comap (localQuotMap P U) ∧ p.comap (localQuotMap P U) ≤ U ∧
        (p.comap (localQuotMap P U)).map (localQuotMap P U) = p
def LocCycleLocalQuot.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime] (J W : Ideal R), P ≤ J → W.IsPrime → P ≤ W →
    W ≤ U → locCycle J W = locCycle (J.map (localQuotMap P U)) (W.map (localQuotMap P U))
def LocalQuotColon.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime] (f g : R),
    ((P ⊔ Ideal.span {f}).colon {g}).map (localQuotMap P U) =
      (Ideal.span {localQuotMap P U f}).colon {localQuotMap P U g}
def LocalQuotFinsum.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P ≤ U →
    ∀ (F : Ideal R → ℤ) (F' : Ideal (localQuot P U) → ℤ),
      (∀ G, F G ≠ 0 → G.IsPrime ∧ P ≤ G ∧ G ≤ U) → (∀ p, F' p ≠ 0 → p.IsPrime) →
      (∀ G : Ideal R, G.IsPrime → P ≤ G → G ≤ U → F G = F' (G.map (localQuotMap P U))) →
      ∑ᶠ G, F G = ∑ᶠ p, F' p
def LocalCoeffLocal.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    (∀ Q₁ Q₂ : Ideal A, Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ → Q₂ < IsLocalRing.maximalIdeal A →
      False) →
    ∀ f g s u v : A, f ≠ 0 → g ≠ 0 → s ≠ 0 → IsUnit u → u * f = v * g →
    (∀ W : Ideal A, locCycle (Ideal.span {s}) W ≠ 0 →
      locCycle (Ideal.span {f}) W = locCycle (Ideal.span {g}) W) →
    ∑ᶠ G, (locCycle (Ideal.span {f}) G - locCycle (Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) =
      ∑ᶠ W, locCycle (Ideal.span {s}) W *
        locCycle (W ⊔ (Ideal.span {f}).colon {g}) (IsLocalRing.maximalIdeal A)
end Lemmas
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


