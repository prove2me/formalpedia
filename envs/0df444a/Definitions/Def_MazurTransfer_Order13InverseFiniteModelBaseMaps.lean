-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseFiniteModelBaseMaps
-- name    : MazurTransfer_Order13InverseFiniteModelBaseMaps
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:29:26.405968+00:00
-- url     : https://prove2.me/theorems/4daed3a5-80bd-432b-8b3d-d962b63d4a8d
-- title:
--   The original structural base maps of the inverse finite model
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. The actual inverse finite coordinate scheme has its specified structural map to $\operatorname{Spec}R$, obtained by composing the polynomial parameter map with the coefficient inclusion. The original recovered reciprocal equivalence also gives the specified $R$-algebra map from the finite coordinate algebra to the positive reciprocal patch. These two literal constructors supply the base-compatibility theorem and the structural section-ring comparison.
-- source:
--   Two original data constructors from MazurTheorem Order13InverseParameterCurveFiniteMap.lean, Apache-2.0, Vas and contributors: inverseFiniteAffineSchemeToBase and candidateToReciprocalPatch. Bodies unchanged; the import uses the public inverse reciprocal-overlap interface. Both original closed types and both original data values are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: original finiteModelToCurve_base and inverse affine-open structural R-algebra section comparison.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transport the actual finite parameter map to the inverse affine
chart, retaining the original inclusion and structural morphism.
Named downstream consumer: the second chart of single-section FiniteMapData for integral Picard.
-/
import Definitions.Def_MazurTransfer_Order13InverseReciprocalOverlapRange

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTorsion.XOneThirteenAffineCurve
open Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

def inverseFiniteAffineSchemeToBase : inverseFiniteAffineScheme R ⟶ Spec (.of R) :=
  inverseFiniteAffineMap R ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))

def candidateToReciprocalPatch (h104 : IsUnit (104 : R)) : candidateAlgebra R →ₐ[R]
    Order13InverseParameterPositiveReciprocalPatch.PatchRing R :=
  (recoveredReciprocalPatchEquiv R h104).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R (candidateAlgebra R) (infinityLocalization R))













end MazurTransfer.Order13InverseParameterFiniteAlgebra




#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.inverseFiniteAffineSchemeToBase
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.candidateToReciprocalPatch


