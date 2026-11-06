-- Prove2me | Definitions.Def_TC433_Algebra_AlgebraicGroup_DiagonalizableGroup_Frobenius_b101475517
-- name    : TC433_Algebra_AlgebraicGroup_DiagonalizableGroup_Frobenius_b101475517
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:17:03.128469+00:00
-- url     : https://prove2.me/theorems/95cf5235-5b05-4219-ad94-f1991c721f83
-- title:
--   TauCeti: Algebra / AlgebraicGroup / DiagonalizableGroup / Frobenius
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Frobenius for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/AlgebraicGroup/DiagonalizableGroup/Frobenius.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_AlgebraicGroup_DiagonalizableGroup_Scheme_Points_56c14399fc
public import Definitions.Def_TC433_Algebra_AlgebraicGroup_Frobenius_Points_7041c2b475

/-!
# Frobenius on diagonalizable groups

Let `A` be a commutative ring of exponential characteristic `p`. For any finitely generated
commutative group `G`, applying the `n`-fold Frobenius of `A` to an `A`-valued point of the
diagonalizable group `D(G)` agrees, under the coordinate-algebra comparison, with the existing
Frobenius endomorphism on convolution points.

## Main result

* `TauCeti.DiagonalizableGroup.groupSchemePointsMulEquiv_mapValue_iterateFrobenius`: the
  scheme-point and convolution-point descriptions of iterated Frobenius agree.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 12 and 13.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti.DiagonalizableGroup

variable {A : Type} [CommRing A]
variable (p n : ℕ) [ExpChar A p]

/-- Under the coordinate-algebra comparison for a diagonalizable group, applying the iterated
Frobenius of the value ring is the existing Frobenius endomorphism on convolution points. -/
theorem groupSchemePointsMulEquiv_mapValue_iterateFrobenius (G : FGCommGrpCat)
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (groupScheme ℤ G).X) :
    groupSchemePointsMulEquiv (R := ℤ) (A := A) G
        ((Spec.map (CommRingCat.ofHom (iterateFrobenius A p n).toIntAlgHom.toRingHom)).asOver
          (Spec (CommRingCat.of ℤ)) ≫ q) =
      Bialgebra.iterateFrobeniusPoints p n
        (groupSchemePointsMulEquiv (R := ℤ) (A := A) G q) := by
  rw [groupSchemePointsMulEquiv_mapValue,
    Bialgebra.iterateFrobeniusPoints_apply, AlgHom.mapValue_apply]

end TauCeti.DiagonalizableGroup


