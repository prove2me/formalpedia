-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:03.044871+00:00
-- url     : https://prove2.me/theorems/9c4bc7d7-9583-4b9e-95f5-8161f7bd2f37
-- title:
--   Injective Of Is Cpt Gen
-- statement:
--   Definitions and structural lemmas for Injective Of Is Cpt Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory
section General
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
def self (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Cpt ξ := ⟨genPt ξ, specializes_refl _⟩
end General
section Affine
variable {R K : Type} [CommRing R] [Field K]
abbrev pt (φ : R →+* K) : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom φ)
def tS (p : Spec (CommRingCat.of R)) : R →+* (Spec (CommRingCat.of R)).presheaf.stalk p :=
  (StructureSheaf.toStalk R p).hom
theorem genPt_asIdeal (φ : R →+* K) : (genPt (pt φ)).asIdeal = RingHom.ker φ := by
  change Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl
end Affine
section Int
def two : Cpt (pt (algebraMap ℤ ℚ)) :=
  ⟨(⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2 Int.prime_two⟩ : PrimeSpectrum ℤ),
    (PrimeSpectrum.le_iff_specializes _ _).1 (by
      change (genPt (pt (algebraMap ℤ ℚ))).asIdeal ≤ _
      rw [genPt_asIdeal, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective ℤ ℚ)]
      exact bot_le)⟩
end Int
end GlobalTheory.CompanionTheory.Ar.CptModel


