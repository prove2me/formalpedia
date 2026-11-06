-- Prove2me | Definitions.Def_TC433_Algebra_AlgebraicGroup_AdditiveGroup_CoordinateBaseChange_dd4e2f0dfc
-- name    : TC433_Algebra_AlgebraicGroup_AdditiveGroup_CoordinateBaseChange_dd4e2f0dfc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:36:14.291197+00:00
-- url     : https://prove2.me/theorems/6d0f7064-ec5f-49e1-b230-01d5829d86a9
-- title:
--   TauCeti: Algebra / AlgebraicGroup / AdditiveGroup / CoordinateBaseChange
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.CoordinateBaseChange for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/AlgebraicGroup/AdditiveGroup/CoordinateBaseChange.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_AlgebraicGroup_AdditiveGroup_BaseChange_0ecaf04073
public import Definitions.Def_TC433_Algebra_AlgebraicGroup_AdditiveGroup_Scheme_e25350ccbe
public import Definitions.Def_TC433_Algebra_AlgebraicGroup_CommHopfAlgCat_BaseChange_e0738e236e
public import Definitions.Def_TC433_RingTheory_Idempotents_Connected_Spectrum_9cf0f4a35f
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Base change of the bundled coordinate Hopf algebra of `𝔾ₐ`

`TauCeti.AdditiveGroup.gaScalarTensorBialgEquiv` identifies `K ⊗[k] O(𝔾ₐ)` with the coordinate
bialgebra of `𝔾ₐ` over `K`. This file bundles that equivalence as an isomorphism in
`CommHopfAlgCat K`, so that the base change of `𝔾ₐ` over `k` *is* `𝔾ₐ` over `K` as a commutative
Hopf algebra, and not merely as a bialgebra.

The bundled base-change isomorphism transports the connectedness of the prime spectrum of the
coordinate algebra over a domain to every scalar extension whose target is a domain.

The antipode needs no separate argument: a bialgebra map between Hopf algebras automatically
commutes with the antipodes, which is what `CommHopfAlgCat.isoMk` uses.

The bundled form is what a consumer of a *presentation* needs. It is an abbreviation so that the
existing simp lemmas for `gaScalarTensorBialgEquiv` apply directly to its forward and inverse
maps. A closed subgroup scheme of a group scheme over `k` is a Hopf-ideal quotient of its coordinate
Hopf algebra; base-changing that presentation produces a quotient of `K ⊗[k] O(G)`, and reading the
result as a closed subgroup scheme over `K` means transporting along an isomorphism in
`CommHopfAlgCat K`. This is the
`𝔾ₐ` companion of `TauCeti.GeneralLinear.coordinateHopfAlgebraBaseChangeIso`, and, as there, the
extension ring's carrier universe must contain the base ring's; the unbundled bialgebra
equivalence has no such restriction.

## Main declarations

* `TauCeti.AdditiveGroup.coordinateHopfAlgebraBaseChangeIso`: the bundled isomorphism.
* `TauCeti.AdditiveGroup.connectedSpace_primeSpectrum_baseChange_coordinateHopfAlgebra`:
  the base-changed coordinate algebra has connected prime spectrum over a domain.

## References

The underlying equivalence is `TauCeti.AdditiveGroup.gaScalarTensorBialgEquiv`, itself the
rank-one case of `TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv`. See W. C. Waterhouse,
*Introduction to Affine Group Schemes*, §1, and J. S. Milne, *Algebraic Groups* (2017), §2.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.AdditiveGroup

universe u v

variable (k : Type u) (K : Type max u v) [CommRing k] [CommRing K] [Algebra k K]

/-- Base change of the bundled coordinate Hopf algebra of `𝔾ₐ` is the coordinate Hopf algebra of
`𝔾ₐ` over the new base. -/
noncomputable abbrev coordinateHopfAlgebraBaseChangeIso :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra k) ≅ coordinateHopfAlgebra K :=
  _root_.CommHopfAlgCat.isoMk (gaScalarTensorBialgEquiv (k := k) (K := K))

/-- The base change of the coordinate Hopf algebra of `𝔾ₐ` has connected prime spectrum
when the extension ring is a domain. -/
theorem connectedSpace_primeSpectrum_baseChange_coordinateHopfAlgebra
    (k : Type u) (K : Type max u v) [CommRing k] [CommRing K] [IsDomain K] [Algebra k K] :
    ConnectedSpace (PrimeSpectrum
      (CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra k))) := by
  let e := coordinateHopfAlgebraBaseChangeIso k K
  have := connectedSpace_primeSpectrum_coordinateHopfAlgebra K
  exact connectedSpace_primeSpectrum_of_injective e.hom.hom.toAlgHom.toRingHom
    (ConcreteCategory.bijective_of_isIso e.hom).1

end TauCeti.AdditiveGroup


