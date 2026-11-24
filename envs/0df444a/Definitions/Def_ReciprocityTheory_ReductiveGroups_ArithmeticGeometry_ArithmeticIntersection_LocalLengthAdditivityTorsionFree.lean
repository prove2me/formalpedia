-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:06.2668+00:00
-- url     : https://prove2.me/theorems/c0f47adf-5e1a-4a40-b489-2d954509bef8
-- title:
--   Local Length Additivity Torsion Free
-- statement:
--   Definitions and structural lemmas for Local Length Additivity Torsion Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LocalLengthAdditivityTorsionFree.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AI
universe u v
open Module
noncomputable def ordMod {A : Type*} [CommRing A] (p : PrimeSpectrum A) (x : A) : ℕ∞ :=
  Ring.ord (A ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal x)
noncomputable def ordLoc {A : Type*} [CommRing A] (p : PrimeSpectrum A) (x : A) : ℕ∞ :=
  Ring.ord (Localization.AtPrime p.asIdeal) (algebraMap A (Localization.AtPrime p.asIdeal) x)
def LocalLengthAdditivity : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (M : Type v) [AddCommGroup M]
    [Module A M] [Module.Finite A M] (x : A),
    ringKrullDim A = 1 →
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) ≠ ⊤ →
    length A (LinearMap.ker (LinearMap.lsmul A M x)) ≠ ⊤ ∧
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) =
      length A (LinearMap.ker (LinearMap.lsmul A M x)) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : ringKrullDim (A ⧸ p.asIdeal) = 1),
          length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
            ordMod p x
def LocalLengthAdditivityTorsionFree : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsTorsionFree A M] (x : A),
    ringKrullDim A = 1 → x ≠ 0 →
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) = (finrank A M : ℕ∞) * Ring.ord A x
def LocalLengthMultiplicativity : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (a b : A),
    ringKrullDim A = 2 → a ≠ 0 → b ≠ 0 →
    length A (A ⧸ Ideal.span {a, b}) ≠ ⊤ →
    (length A (A ⧸ Ideal.span {a, b}) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal),
          ordLoc p a * ordMod p b) ∧
    (length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧
     length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≠ ⊤) ∧
    (∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal), ordLoc p a * ordMod p b) =
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ b ∈ p.asIdeal), ordLoc p b * ordMod p a
end ReciprocityTheory.ChartRestriction.G.AI


