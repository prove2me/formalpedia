-- Prove2me | Definitions.Def_MazurTransfer_Order13CoordinateBaseChangeMaps
-- name    : MazurTransfer_Order13CoordinateBaseChangeMaps
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T03:11:46.17566+00:00
-- url     : https://prove2.me/theorems/6365e24c-0609-4549-a650-33df1a41a64c
-- title:
--   Actual chart and overlap ring maps under scalar extension
-- statement:
--   Let $R$ and $S$ be commutative rings with an $R$-algebra structure on $S$. Write $A_R,B_R$ for the ordinary and reciprocal quadratic coordinate rings of the order-thirteen curve, and $A_R[x_R^{-1}],B_R[z_R^{-1}]$ for their overlap localizations. The specified scalar-extension equivalences induce ring maps $\phi_A:A_R\to A_S$ and $\phi_B:B_R\to B_S$, and localized maps $\lambda_A,\lambda_B$ satisfying
--   $$\lambda_A(\iota_R(a))=\iota_S(\phi_A(a)),\qquad\lambda_B(\iota_R(b))=\iota_S(\phi_B(b)).$$
--   Here $a\in A_R$, $b\in B_R$, and $\iota$ denotes the relevant localization map. The maps preserve the actual coordinates and send the distinguished inverses of $x_R,z_R$ to those of $x_S,z_S$.
--
--   The file bundles the four already proved coordinate identities with these concrete constructors and their elementary compatibility properties. It supplies the maps used to prove naturality of the actual reciprocal transition and hence the curve base-change square.
-- source:
--   Merged checked declaration bodies from Order13CoordinateBaseChangeGenerators.lean and Order13CoordinateBaseChangeLocalizationMaps.lean. The four coordinate properties forward to the separate Proved public theorem MazurTransfer.order13_coordinate_base_change_preserves_generators; all localization constructor and proof bodies are unchanged. Exact Lean syntax-oracle header ranges and section boundaries are recorded, and all 21 original closed kernel types are checked. Vas and contributors, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual quadratic chart base-change isomorphisms preserve
the abscissa and ordinate generators. Named downstream consumer: checking
compatibility with the literal reciprocal localization transition when
identifying the glued integral curve's rational and finite-field fibres.
-/
import Definitions.Def_MazurTransfer_Order13CoordinateAlgebraBaseChange
import Theorems.Thm_MazurTransfer_order13_coordinate_base_change_preserves_generators


noncomputable section
namespace MazurTransfer.Order13CoordinateBaseChange
open Polynomial Algebra TensorProduct
universe u v
variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]







theorem ordinaryCoordinateRingEquiv_y :
    ordinaryCoordinateRingEquiv R S
      (1 ⊗ₜ[R] MazurTorsion.XOneThirteenAffineCurve.yCoordinate R) =
      MazurTorsion.XOneThirteenAffineCurve.yCoordinate S  := by exact (_root_.MazurTransfer.order13_coordinate_base_change_preserves_generators R S).2.1

theorem ordinaryCoordinateRingEquiv_x :
    ordinaryCoordinateRingEquiv R S
      (1 ⊗ₜ[R] MazurTorsion.XOneThirteenAffineCurve.xCoordinate R) =
      MazurTorsion.XOneThirteenAffineCurve.xCoordinate S  := by exact (_root_.MazurTransfer.order13_coordinate_base_change_preserves_generators R S).1

theorem reciprocalCoordinateRingEquiv_w :
    reciprocalCoordinateRingEquiv R S
      (1 ⊗ₜ[R] MazurTorsion.XOneThirteenProjectiveCurve.wCoordinate R) =
      MazurTorsion.XOneThirteenProjectiveCurve.wCoordinate S  := by exact (_root_.MazurTransfer.order13_coordinate_base_change_preserves_generators R S).2.2.2

theorem reciprocalCoordinateRingEquiv_z :
    reciprocalCoordinateRingEquiv R S
      (1 ⊗ₜ[R] MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate R) =
      MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate S  := by exact (_root_.MazurTransfer.order13_coordinate_base_change_preserves_generators R S).2.2.1

end MazurTransfer.Order13CoordinateBaseChange








#print axioms MazurTransfer.Order13CoordinateBaseChange.ordinaryCoordinateRingEquiv_x
#print axioms MazurTransfer.Order13CoordinateBaseChange.reciprocalCoordinateRingEquiv_w

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual change-of-base ring maps on the two quadratic
charts and their principal-open overlaps, preserving coordinates and
their distinguished inverses. Named downstream consumer: compatibility
of the order-thirteen gluing transition with arbitrary base change.
-/



noncomputable section
namespace MazurTransfer.Order13CoordinateBaseChange
open Polynomial Algebra TensorProduct
universe u v
variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

def ordinaryRingMap : CoordinateRing R →+* CoordinateRing S :=
  (ordinaryCoordinateRingEquiv R S).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := CoordinateRing R)).toRingHom

def reciprocalRingMap : ReciprocalRing R →+* ReciprocalRing S :=
  (reciprocalCoordinateRingEquiv R S).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := ReciprocalRing R)).toRingHom

theorem ordinaryRingMap_x : ordinaryRingMap R S (xCoordinate R) = xCoordinate S :=
  ordinaryCoordinateRingEquiv_x R S

theorem ordinaryRingMap_y : ordinaryRingMap R S (yCoordinate R) = yCoordinate S :=
  ordinaryCoordinateRingEquiv_y R S

theorem reciprocalRingMap_z : reciprocalRingMap R S (zCoordinate R) = zCoordinate S :=
  reciprocalCoordinateRingEquiv_z R S

theorem reciprocalRingMap_w : reciprocalRingMap R S (wCoordinate R) = wCoordinate S :=
  reciprocalCoordinateRingEquiv_w R S

theorem ordinaryRingMap_algebraMap (r : R) :
    ordinaryRingMap R S (algebraMap R (CoordinateRing R) r) =
      algebraMap S (CoordinateRing S) (algebraMap R S r) := by
  change ordinaryCoordinateRingEquiv R S (1 ⊗ₜ[R] algebraMap R (CoordinateRing R) r) = _
  rw [← Algebra.TensorProduct.algebraMap_apply',
    IsScalarTower.algebraMap_apply R S (S ⊗[R] CoordinateRing R)]
  exact (ordinaryCoordinateRingEquiv R S).commutes _

theorem reciprocalRingMap_algebraMap (r : R) :
    reciprocalRingMap R S (algebraMap R (ReciprocalRing R) r) =
      algebraMap S (ReciprocalRing S) (algebraMap R S r) := by
  change reciprocalCoordinateRingEquiv R S (1 ⊗ₜ[R] algebraMap R (ReciprocalRing R) r) = _
  rw [← Algebra.TensorProduct.algebraMap_apply',
    IsScalarTower.algebraMap_apply R S (S ⊗[R] ReciprocalRing R)]
  exact (reciprocalCoordinateRingEquiv R S).commutes _

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

theorem ordinaryOverlapRingMap_algebraMap (a : CoordinateRing R) :
    ordinaryOverlapRingMap R S (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) a) =
      algebraMap (CoordinateRing S) (OrdinaryOverlapRing S) (ordinaryRingMap R S a) :=
  localizationAwayMap_algebraMap _ _ _ _ a

theorem reciprocalOverlapRingMap_algebraMap (a : ReciprocalRing R) :
    reciprocalOverlapRingMap R S (algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R) a) =
      algebraMap (ReciprocalRing S) (ReciprocalOverlapRing S) (reciprocalRingMap R S a) :=
  localizationAwayMap_algebraMap _ _ _ _ a

theorem ordinaryOverlapRingMap_invSelf :
    ordinaryOverlapRingMap R S (IsLocalization.Away.invSelf (xCoordinate R)) =
      IsLocalization.Away.invSelf (xCoordinate S) :=
  localizationAwayMap_invSelf _ _ _ _

theorem reciprocalOverlapRingMap_invSelf :
    reciprocalOverlapRingMap R S (IsLocalization.Away.invSelf (zCoordinate R)) =
      IsLocalization.Away.invSelf (zCoordinate S) :=
  localizationAwayMap_invSelf _ _ _ _

end MazurTransfer.Order13CoordinateBaseChange

#print axioms MazurTransfer.Order13CoordinateBaseChange.ordinaryRingMap_x
#print axioms MazurTransfer.Order13CoordinateBaseChange.reciprocalRingMap_w
#print axioms MazurTransfer.Order13CoordinateBaseChange.localizationAwayMap_invSelf
#print axioms MazurTransfer.Order13CoordinateBaseChange.ordinaryOverlapRingMap_invSelf
#print axioms MazurTransfer.Order13CoordinateBaseChange.reciprocalOverlapRingMap_invSelf

end


