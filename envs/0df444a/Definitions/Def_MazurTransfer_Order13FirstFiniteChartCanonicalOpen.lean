-- Prove2me | Definitions.Def_MazurTransfer_Order13FirstFiniteChartCanonicalOpen
-- name    : MazurTransfer_Order13FirstFiniteChartCanonicalOpen
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:36:25.181474+00:00
-- url     : https://prove2.me/theorems/d79c0379-f2d1-4db0-8080-bc6d39bdf0fa
-- title:
--   The original first-chart open with its exact public-chart identity
-- statement:
--   Let $R$ be a commutative ring. Put $\delta=(w-1-z-z^3)(w-1-z+z^3)$ in the actual reciprocal coordinate ring. The original first-chart open is the union of the ordinary-chart image and the reciprocal principal-open image $D(\delta)$. The original coordinate, localization, spectral-map and open-image constructors are retained. This original open is definitionally equal to the first-chart open supplied by the public affine-complement theorem.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Eight original constructors from Order13SingleSectionReciprocalPatch.lean and Order13ActualPositiveInfinityComplement.lean, with every body unchanged, plus one reflexive identity with the published first-chart open. All eight original closed types and construction values are compared in the kernel. The structural identity is proved by reflexivity, with no change of curve, open subset or selected first-chart presentation. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumers: actual first/inverse chart overlap, structural section R-algebra comparisons, and unchanged integral FiniteMapData.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original positive-section-complement chart constructors, with their actual first finite-chart identity.
Named downstream consumer: actual first/inverse chart overlap and unchanged integral FiniteMapData. All eight original constructor bodies are retained. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartFromPublicTheorem
noncomputable section
universe u
namespace MazurTransfer.Order13SingleSectionReciprocalPatch
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]
def d : ReciprocalRing R := wCoordinate R - 1 - zCoordinate R - zCoordinate R ^ 3

def dPrime : ReciprocalRing R := wCoordinate R - 1 - zCoordinate R + zCoordinate R ^ 3

abbrev PatchRing := Localization.Away (d R * dPrime R)

end MazurTransfer.Order13SingleSectionReciprocalPatch

namespace MazurTransfer.Order13ActualPositiveInfinityComplement
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13SingleSectionReciprocalPatch
variable (R : Type u) [CommRing R]
def reciprocalPatchInclusion : Spec (.of (PatchRing R)) ⟶ reciprocalScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R) (PatchRing R)))

instance reciprocalPatchInclusion_isOpenImmersion : IsOpenImmersion (reciprocalPatchInclusion R) :=
  IsOpenImmersion.of_isLocalization (d R * dPrime R)

def reciprocalPatchChartMap : Spec (.of (PatchRing R)) ⟶ curveScheme R :=
  reciprocalPatchInclusion R ≫ reciprocalChartMap R

instance reciprocalPatchChartMap_isOpenImmersion : IsOpenImmersion (reciprocalPatchChartMap R) :=
  IsOpenImmersion.comp (reciprocalPatchInclusion R) (reciprocalChartMap R)

def sectionComplementOpen : (curveScheme R).Opens :=
  (ordinaryChartMap R).opensRange ⊔ (reciprocalPatchChartMap R).opensRange

end MazurTransfer.Order13ActualPositiveInfinityComplement

theorem MazurTransfer.Order13ActualPositiveInfinityComplement.sectionComplementOpen_eq_public_first_chart
    (R : Type u) [CommRing R] : sectionComplementOpen R =
      MazurTransfer.Order13FirstFiniteChartFromPublicTheorem.chartOpen R := rfl
#print axioms MazurTransfer.Order13ActualPositiveInfinityComplement.sectionComplementOpen
#print axioms MazurTransfer.Order13ActualPositiveInfinityComplement.sectionComplementOpen_eq_public_first_chart


