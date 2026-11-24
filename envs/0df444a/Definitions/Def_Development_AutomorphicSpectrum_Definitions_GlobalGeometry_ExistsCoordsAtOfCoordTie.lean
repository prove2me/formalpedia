-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:43.049697+00:00
-- url     : https://prove2.me/theorems/eeec22d9-7fa3-4677-ba86-9ad803825e3c
-- title:
--   Exists Coords At Of Coord Tie
-- statement:
--   Definitions and structural lemmas for Exists Coords At Of Coord Tie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsCoordsAtOfCoordTie.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.CoordModel
open AlgebraicGeometry CategoryTheory
variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]
def gen : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A Ω))
def pr (p : Spec (CommRingCat.of A)) : PrimeSpectrum A := p
def toSt (p : Spec (CommRingCat.of A)) : A →+* (Spec (CommRingCat.of A)).presheaf.stalk p :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec (CommRingCat.of A)).presheaf.germ ⊤ p trivial).hom
variable [IsDomain A] [IsFractionRing A Ω]
section General
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X}
end General
end GlobalTheory.CompanionTheory.Ar.CoordModel


