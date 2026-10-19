-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseOverlapSchemeMaps
-- name    : MazurTransfer_Order13InverseOverlapSchemeMaps
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:14:44.779926+00:00
-- url     : https://prove2.me/theorems/b80afae9-ebed-41cc-bb9a-93f2a2a82b89
-- title:
--   The two literal maps from the inverse-atlas common affine source
-- statement:
--   For a noetherian commutative integral domain $R$ with $104$ invertible, the literal common localization of the inverse finite chart maps to the ordinary parameter localization and to the retained positive reciprocal patch. These are the original spectral maps induced by the localization inclusion and recovered reciprocal algebra equivalence. Their compatibility and pullback property are separate obligations used by the inverse finite-chart gluing theorem.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. The two original data constructors from Order13InverseParameterOverlapSchemeMaps.lean, with unchanged bodies. The separate proof-only overlap comparisons are excluded and will occur in theorem submissions. Both original closed types and both original data values are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: global inverse finite-chart gluing and actual integral FiniteMapData.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal common affine chart is the categorical
intersection of the ordinary parameter and positive reciprocal maps into the inverse finite model.
Named downstream consumer: compatibility and global inverse-chart gluing.
No global comparison is assumed.
-/
import Definitions.Def_MazurTransfer_Order13InverseReciprocalOverlapRange

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

def ordinaryInfinityChartMap : Spec (.of (ordinaryInfinityLocalization R)) ⟶
    Spec (.of (ordinaryParameterLocalization R)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ordinaryParameterLocalization R) (ordinaryInfinityLocalization R)))

def ordinaryInfinityToReciprocalPatch (h104 : IsUnit (104 : R)) :
    Spec (.of (ordinaryInfinityLocalization R)) ⟶
      Spec (.of (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)) :=
  Spec.map (CommRingCat.ofHom
    ((infinityLocalizedInclusion R).comp (recoveredReciprocalPatchEquiv R h104).toAlgHom).toRingHom)









end MazurTransfer.Order13InverseParameterFiniteAlgebra



#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.ordinaryInfinityChartMap
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.ordinaryInfinityToReciprocalPatch


