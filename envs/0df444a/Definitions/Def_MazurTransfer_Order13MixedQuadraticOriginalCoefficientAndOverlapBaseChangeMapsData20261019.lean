-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalCoefficientAndOverlapBaseChangeMapsData20261019
-- name    : MazurTransfer_Order13MixedQuadraticOriginalCoefficientAndOverlapBaseChangeMapsData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T04:57:24.155164+00:00
-- url     : https://prove2.me/theorems/b823a74a-6ba9-4a32-af1a-bff1e2a80532
-- title:
--   Original mixed quadratic coefficient and overlap base-change maps
-- statement:
--   The original coefficient-change homomorphisms for both literal mixed quadratic charts and both principal overlap localizations, with their original coordinate and distinguished-inverse identities. Thirty-one original public types, five whole nonproof values and the referenced original constructor helper type are checked. Named downstream consumer: the actual whole-curve cartesian base square.
-- source:
--   MazurTheorem complete original mixed quadratic coefficient maps, transition naturality, gluing and whole base-change square; Vas and contributors; Apache-2.0.

import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalRationalChartComparisonAndAffineBaseChangeData20261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalOverlapAlgebraData20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual quadratic chart base-change isomorphisms preserve
the abscissa and ordinate generators. Named downstream consumer: checking
compatibility with the literal reciprocal localization transition when
identifying the glued integral curve's rational and finite-field fibres.
-/
noncomputable section
namespace MazurTransfer.MixedQuadraticBaseChangeOriginalConstructorProofHelpers20261019
open Polynomial Algebra TensorProduct
universe u v
variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
theorem quadraticEquationEquiv_of (p q : Polynomial (Polynomial S))
    (h : p = q) (s : Polynomial S) :
    AdjoinRoot.algEquivOfEq S p q h (AdjoinRoot.of p s) = AdjoinRoot.of q s := by
  cases h
  simp [AdjoinRoot.algEquivOfEq, AdjoinRoot.algEquivOfAssociated,
    AdjoinRoot.mapAlgEquiv, AdjoinRoot.mapAlgHom, AdjoinRoot.map]

end MazurTransfer.MixedQuadraticBaseChangeOriginalConstructorProofHelpers20261019
end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the checked tensor generator proof of Order13CoordinateBaseChangeGenerators
from the existing square model to the literal mixed quadratic equations.
Design boundary: both genuine mixed chart scalar-extension equivalences
preserve all four coordinates. Named downstream consumer: whole mixed
curve change of coefficients and its cartesian base square.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticCoefficientBaseChange
open Polynomial Algebra TensorProduct
open MixedQuadraticCoordinateJacobian Order13MixedQuadraticJacobianCertificates
open Order13MixedQuadraticAffineBaseChange Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticOverlapCoordinates
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem coordinateRingEquiv_root (h f : Polynomial R) :
    MixedQuadraticCoordinateBaseChange.coordinateRingEquiv R S h f
      (1 ⊗ₜ[R] AdjoinRoot.root (equation R h f)) =
      AdjoinRoot.root (equation S (h.map (algebraMap R S)) (f.map (algebraMap R S))) := by
  unfold MixedQuadraticCoordinateBaseChange.coordinateRingEquiv
  rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root]
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

theorem coordinateRingEquiv_of (h f p : Polynomial R) :
    MixedQuadraticCoordinateBaseChange.coordinateRingEquiv R S h f
      (1 ⊗ₜ[R] AdjoinRoot.of (equation R h f) p) =
      AdjoinRoot.of (equation S (h.map (algebraMap R S)) (f.map (algebraMap R S)))
        (p.map (algebraMap R S)) := by
  unfold MixedQuadraticCoordinateBaseChange.coordinateRingEquiv
  rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_of]
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]
  change AdjoinRoot.of (equation S (h.map (algebraMap R S)) (f.map (algebraMap R S)))
    ((polyEquivTensor' R S).symm (1 ⊗ₜ[R] p)) = _
  apply congrArg (AdjoinRoot.of (equation S (h.map (algebraMap R S)) (f.map (algebraMap R S))))
  exact (polyEquivTensor_symm_apply_tmul_eq_smul R S 1 p).trans (one_smul S _)

theorem ordinaryAlgebraEquiv_y :
    ordinaryAlgebraEquiv R S (1 ⊗ₜ[R] yCoordinate R) = yCoordinate S := by
  unfold yCoordinate
  unfold ordinaryAlgebraEquiv
  rw [AlgEquiv.trans_apply, coordinateRingEquiv_root, AdjoinRoot.algEquivOfEq_root]

theorem ordinaryAlgebraEquiv_x :
    ordinaryAlgebraEquiv R S (1 ⊗ₜ[R] xCoordinate R) = xCoordinate S := by
  unfold xCoordinate
  unfold ordinaryAlgebraEquiv
  rw [AlgEquiv.trans_apply, coordinateRingEquiv_of, Polynomial.map_X,
    MazurTransfer.MixedQuadraticBaseChangeOriginalConstructorProofHelpers20261019.quadraticEquationEquiv_of]

theorem reciprocalAlgebraEquiv_w :
    reciprocalAlgebraEquiv R S (1 ⊗ₜ[R] wCoordinate R) = wCoordinate S := by
  unfold wCoordinate
  unfold reciprocalAlgebraEquiv
  rw [AlgEquiv.trans_apply, coordinateRingEquiv_root, AdjoinRoot.algEquivOfEq_root]

theorem reciprocalAlgebraEquiv_z :
    reciprocalAlgebraEquiv R S (1 ⊗ₜ[R] zCoordinate R) = zCoordinate S := by
  unfold zCoordinate
  unfold reciprocalAlgebraEquiv
  rw [AlgEquiv.trans_apply, coordinateRingEquiv_of, Polynomial.map_X,
    MazurTransfer.MixedQuadraticBaseChangeOriginalConstructorProofHelpers20261019.quadraticEquationEquiv_of]

end MazurTransfer.Order13MixedQuadraticCoefficientBaseChange
#print axioms MazurTransfer.Order13MixedQuadraticCoefficientBaseChange.ordinaryAlgebraEquiv_x
#print axioms MazurTransfer.Order13MixedQuadraticCoefficientBaseChange.ordinaryAlgebraEquiv_y
#print axioms MazurTransfer.Order13MixedQuadraticCoefficientBaseChange.reciprocalAlgebraEquiv_z
#print axioms MazurTransfer.Order13MixedQuadraticCoefficientBaseChange.reciprocalAlgebraEquiv_w

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from the complete checked Order13CoordinateBaseChangeLocalizationMaps proof,
with the actual mixed quadratic rings and gluing object throughout.
Design boundary: actual change-of-base ring maps on the two quadratic
charts and their principal-open overlaps, preserving coordinates and
their distinguished inverses. Named downstream consumer: compatibility
of the order-thirteen gluing transition with arbitrary base change.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticCoefficientBaseChange
open Polynomial Algebra TensorProduct
open Order13MixedQuadraticAffineBaseChange
universe u
variable (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
open Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticOverlapCoordinates

def ordinaryRingMap : ordinaryCoordinateRing R →+* ordinaryCoordinateRing S :=
  (ordinaryAlgebraEquiv R S).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := ordinaryCoordinateRing R)).toRingHom

def reciprocalRingMap : reciprocalCoordinateRing R →+* reciprocalCoordinateRing S :=
  (reciprocalAlgebraEquiv R S).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := reciprocalCoordinateRing R)).toRingHom

theorem ordinaryRingMap_x : ordinaryRingMap R S (xCoordinate R) = xCoordinate S :=
  ordinaryAlgebraEquiv_x R S

theorem ordinaryRingMap_y : ordinaryRingMap R S (yCoordinate R) = yCoordinate S :=
  ordinaryAlgebraEquiv_y R S

theorem reciprocalRingMap_z : reciprocalRingMap R S (zCoordinate R) = zCoordinate S :=
  reciprocalAlgebraEquiv_z R S

theorem reciprocalRingMap_w : reciprocalRingMap R S (wCoordinate R) = wCoordinate S :=
  reciprocalAlgebraEquiv_w R S

theorem ordinaryRingMap_algebraMap (r : R) :
    ordinaryRingMap R S (algebraMap R (ordinaryCoordinateRing R) r) =
      algebraMap S (ordinaryCoordinateRing S) (algebraMap R S r) := by
  change ordinaryAlgebraEquiv R S (1 ⊗ₜ[R] algebraMap R (ordinaryCoordinateRing R) r) = _
  rw [← Algebra.TensorProduct.algebraMap_apply',
    IsScalarTower.algebraMap_apply R S (S ⊗[R] ordinaryCoordinateRing R)]
  exact (ordinaryAlgebraEquiv R S).commutes _

theorem reciprocalRingMap_algebraMap (r : R) :
    reciprocalRingMap R S (algebraMap R (reciprocalCoordinateRing R) r) =
      algebraMap S (reciprocalCoordinateRing S) (algebraMap R S r) := by
  change reciprocalAlgebraEquiv R S (1 ⊗ₜ[R] algebraMap R (reciprocalCoordinateRing R) r) = _
  rw [← Algebra.TensorProduct.algebraMap_apply',
    IsScalarTower.algebraMap_apply R S (S ⊗[R] reciprocalCoordinateRing R)]
  exact (reciprocalAlgebraEquiv R S).commutes _

def localizationAwayMap {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (f : A →+* B) (x : A) (y : B) (h : f x = y) :
    Localization.Away x →+* Localization.Away y :=
  IsLocalization.Away.lift x
    (g := (algebraMap B (Localization.Away y)).comp f)
    (by
      change IsUnit (algebraMap B (Localization.Away y) (f x))
      rw [h]
      exact IsLocalization.Away.algebraMap_isUnit y)

theorem localizationAwayMap_algebraMap {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (f : A →+* B) (x : A) (y : B) (h : f x = y) (a : A) :
    localizationAwayMap f x y h (algebraMap A (Localization.Away x) a) =
      algebraMap B (Localization.Away y) (f a) :=
  IsLocalization.Away.lift_eq x _ a

theorem localizationAwayMap_invSelf {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (f : A →+* B) (x : A) (y : B) (h : f x = y) :
    localizationAwayMap f x y h (IsLocalization.Away.invSelf x) =
      IsLocalization.Away.invSelf y := by
  have hu : IsUnit (algebraMap B (Localization.Away y) y) :=
    IsLocalization.Away.algebraMap_isUnit y
  apply hu.mul_right_inj.mp
  calc
    _ = localizationAwayMap f x y h
        (algebraMap A (Localization.Away x) x * IsLocalization.Away.invSelf x) := by
      rw [map_mul, localizationAwayMap_algebraMap, h]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := (IsLocalization.Away.mul_invSelf y).symm

def ordinaryOverlapRingMap : OrdinaryOverlapRing R →+* OrdinaryOverlapRing S :=
  localizationAwayMap (ordinaryRingMap R S) (xCoordinate R) (xCoordinate S)
    (ordinaryRingMap_x R S)

def reciprocalOverlapRingMap : ReciprocalOverlapRing R →+* ReciprocalOverlapRing S :=
  localizationAwayMap (reciprocalRingMap R S) (zCoordinate R) (zCoordinate S)
    (reciprocalRingMap_z R S)

theorem ordinaryOverlapRingMap_algebraMap (a : ordinaryCoordinateRing R) :
    ordinaryOverlapRingMap R S (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) a) =
      algebraMap (ordinaryCoordinateRing S) (OrdinaryOverlapRing S) (ordinaryRingMap R S a) :=
  localizationAwayMap_algebraMap _ _ _ _ a

theorem reciprocalOverlapRingMap_algebraMap (a : reciprocalCoordinateRing R) :
    reciprocalOverlapRingMap R S (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R) a) =
      algebraMap (reciprocalCoordinateRing S) (ReciprocalOverlapRing S) (reciprocalRingMap R S a) :=
  localizationAwayMap_algebraMap _ _ _ _ a

theorem ordinaryOverlapRingMap_invSelf :
    ordinaryOverlapRingMap R S (IsLocalization.Away.invSelf (xCoordinate R)) =
      IsLocalization.Away.invSelf (xCoordinate S) :=
  localizationAwayMap_invSelf _ _ _ _

theorem reciprocalOverlapRingMap_invSelf :
    reciprocalOverlapRingMap R S (IsLocalization.Away.invSelf (zCoordinate R)) =
      IsLocalization.Away.invSelf (zCoordinate S) :=
  localizationAwayMap_invSelf _ _ _ _

end MazurTransfer.Order13MixedQuadraticCoefficientBaseChange

#print axioms MazurTransfer.Order13MixedQuadraticCoefficientBaseChange.ordinaryRingMap_x
#print axioms MazurTransfer.Order13MixedQuadraticCoefficientBaseChange.reciprocalRingMap_w
#print axioms MazurTransfer.Order13MixedQuadraticCoefficientBaseChange.localizationAwayMap_invSelf
#print axioms MazurTransfer.Order13MixedQuadraticCoefficientBaseChange.ordinaryOverlapRingMap_invSelf
#print axioms MazurTransfer.Order13MixedQuadraticCoefficientBaseChange.reciprocalOverlapRingMap_invSelf

end


