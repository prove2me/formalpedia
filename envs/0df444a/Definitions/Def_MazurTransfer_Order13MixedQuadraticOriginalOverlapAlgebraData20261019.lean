-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalOverlapAlgebraData20261019
-- name    : MazurTransfer_Order13MixedQuadraticOriginalOverlapAlgebraData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T04:16:45.235934+00:00
-- url     : https://prove2.me/theorems/47573adb-e3fb-48f0-8365-b91cac5e29ed
-- title:
--   Original integral mixed quadratic overlap algebra
-- statement:
--   The original mixed quadratic coordinates and principal localization rings, the two explicit inverse overlap homomorphisms, and the whole original algebra equivalence. Forty-eight original types and seventeen whole values are checked. The maps implement inverse abscissas and ordinate rescaling by the inverse cube over every commutative ring. Named downstream consumer: the original dyadic two-chart scheme gluing.
-- source:
--   MazurTheorem original mixed quadratic integral charts, overlap and gluing, by Vasily Ilin and contributors; Apache-2.0. Original attribution retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalPolynomialsAndJacobianCoefficientData20261019
import Definitions.Def_MazurTransfer_MixedQuadraticOriginalCoordinateEquationAndJacobianData20261019
import Definitions.Def_MazurTransfer_Order13DyadicMixedOriginalAffineChartData20261019
import Theorems.Thm_MazurTransfer_mixed_quadratic_reciprocal_equations
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the coordinate algebra y^2+h(x)y=f(x), its actual
Jacobian elements and first-order error across square-zero corrections.
Named downstream consumer: the mixed quadratic integral model at two.
-/
noncomputable section
namespace MazurTransfer.MixedQuadraticCoordinateJacobian
open Polynomial
universe u v
variable (R : Type u) [CommRing R]

theorem root_relation (h f : Polynomial R) :
    AdjoinRoot.root (equation R h f) ^ 2 +
      AdjoinRoot.of (equation R h f) h * AdjoinRoot.root (equation R h f) -
      AdjoinRoot.of (equation R h f) f = 0 := by
  have ht := AdjoinRoot.eval₂_root (equation R h f)
  change eval₂ (AdjoinRoot.of (equation R h f)) (AdjoinRoot.root (equation R h f))
    (X ^ 2 + C h * X - C f) = 0 at ht
  simpa only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C] using ht

end MazurTransfer.MixedQuadraticCoordinateJacobian
end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: evaluate the actual mixed quadratic chart polynomials
and their derivatives under arbitrary coefficient-ring homomorphisms.
Named downstream consumer: their integral Jacobian smoothness certificates.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticPolynomialEvaluations
open Polynomial Order13MixedQuadraticJacobianCertificates
universe u v
variable (R : Type u) [CommRing R] {A : Type v} [CommRing A] (ι : Polynomial R →+* A)

theorem map_ordinaryH : ι (ordinaryH R) = ι X ^ 3 + ι X ^ 2 + 1 := by
  change ι (X ^ 3 + X ^ 2 + 1) = _
  rw [map_add, map_add, map_pow, map_pow, map_one]
theorem map_ordinaryF : ι (ordinaryF R) = ι X * (ι X + 1) := by
  change ι (X * (X + 1)) = _
  rw [map_mul, map_add, map_one]
theorem map_reciprocalH : ι (reciprocalH R) = 1 + ι X + ι X ^ 3 := by
  change ι (1 + X + X ^ 3) = _
  rw [map_add, map_add, map_one, map_pow]
theorem map_reciprocalF : ι (reciprocalF R) = ι X ^ 4 + ι X ^ 5 := by
  change ι (X ^ 4 + X ^ 5) = _
  rw [map_add, map_pow, map_pow]

end MazurTransfer.Order13MixedQuadraticPolynomialEvaluations
end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal integral mixed quadratic chart equations
transform under x*z=1 and ordinate rescaling by the inverse cube, without
inverting two. Named downstream consumer: actual dyadic overlap ring maps.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticReciprocalRelations
universe u
variable (R : Type u) [CommRing R]

theorem reciprocal_relation (x y z : R) (hxz : x * z = 1)
    (hy : y ^ 2 + (x ^ 3 + x ^ 2 + 1) * y - x * (x + 1) = 0) :
    (y * z ^ 3) ^ 2 + (1 + z + z ^ 3) * (y * z ^ 3) - (z ^ 4 + z ^ 5) = 0 := by
  exact (MazurTransfer.mixed_quadratic_reciprocal_equations R x z hxz).1 y hy

theorem ordinary_relation (z w x : R) (hzx : z * x = 1)
    (hw : w ^ 2 + (1 + z + z ^ 3) * w - (z ^ 4 + z ^ 5) = 0) :
    (w * x ^ 3) ^ 2 + (x ^ 3 + x ^ 2 + 1) * (w * x ^ 3) - x * (x + 1) = 0 := by
  have hxz : x * z = 1 := (mul_comm x z).trans hzx
  exact (MazurTransfer.mixed_quadratic_reciprocal_equations R x z hxz).2 w hw

end MazurTransfer.Order13MixedQuadraticReciprocalRelations
end
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Vas and contributors.
Released under Apache-2.0. Authors: Vasily Ilin.
The coordinate and localization setup adapts the existing order-thirteen
projective-chart construction to the mixed quadratic integral equations.
Design boundary: actual chart coordinates and their principal localizations.
Named downstream consumer: inverse overlap maps and the dyadic glued curve.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticOverlapCoordinates
open Polynomial MixedQuadraticCoordinateJacobian
open Order13MixedQuadraticJacobianCertificates Order13MixedQuadraticPolynomialEvaluations
open Order13DyadicMixedQuadraticCharts
universe u
variable (R : Type u) [CommRing R]

def xCoordinate : ordinaryCoordinateRing R := AdjoinRoot.of (equation R (ordinaryH R) (ordinaryF R)) X
def yCoordinate : ordinaryCoordinateRing R := AdjoinRoot.root (equation R (ordinaryH R) (ordinaryF R))
def zCoordinate : reciprocalCoordinateRing R := AdjoinRoot.of (equation R (reciprocalH R) (reciprocalF R)) X
def wCoordinate : reciprocalCoordinateRing R := AdjoinRoot.root (equation R (reciprocalH R) (reciprocalF R))

theorem ordinary_relation : yCoordinate R ^ 2 +
    (xCoordinate R ^ 3 + xCoordinate R ^ 2 + 1) * yCoordinate R -
    xCoordinate R * (xCoordinate R + 1) = 0 := by
  have ht := root_relation R (ordinaryH R) (ordinaryF R)
  rw [map_ordinaryH R _, map_ordinaryF R _] at ht
  exact ht

theorem reciprocal_relation : wCoordinate R ^ 2 +
    (1 + zCoordinate R + zCoordinate R ^ 3) * wCoordinate R -
    (zCoordinate R ^ 4 + zCoordinate R ^ 5) = 0 := by
  have ht := root_relation R (reciprocalH R) (reciprocalF R)
  rw [map_reciprocalH R _, map_reciprocalF R _] at ht
  exact ht

abbrev OrdinaryOverlapRing := Localization.Away (xCoordinate R)
abbrev ReciprocalOverlapRing := Localization.Away (zCoordinate R)

def ordinaryX : OrdinaryOverlapRing R := algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) (xCoordinate R)
def ordinaryY : OrdinaryOverlapRing R := algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) (yCoordinate R)
def reciprocalZ : ReciprocalOverlapRing R := algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R) (zCoordinate R)
def reciprocalW : ReciprocalOverlapRing R := algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R) (wCoordinate R)
def inverseX : OrdinaryOverlapRing R := IsLocalization.Away.invSelf (xCoordinate R)
def inverseZ : ReciprocalOverlapRing R := IsLocalization.Away.invSelf (zCoordinate R)

theorem ordinaryX_inverseX : ordinaryX R * inverseX R = 1 := IsLocalization.Away.mul_invSelf _
theorem reciprocalZ_inverseZ : reciprocalZ R * inverseZ R = 1 := IsLocalization.Away.mul_invSelf _

theorem inverseX_isUnit : IsUnit (inverseX R) := by
  apply isUnit_iff_exists_inv.mpr
  exact ⟨ordinaryX R, by rw [mul_comm, ordinaryX_inverseX]⟩
theorem inverseZ_isUnit : IsUnit (inverseZ R) := by
  apply isUnit_iff_exists_inv.mpr
  exact ⟨reciprocalZ R, by rw [mul_comm, reciprocalZ_inverseZ]⟩

theorem ordinary_overlap_relation : ordinaryY R ^ 2 +
    (ordinaryX R ^ 3 + ordinaryX R ^ 2 + 1) * ordinaryY R -
    ordinaryX R * (ordinaryX R + 1) = 0 := by
  simpa only [ordinaryX, ordinaryY, map_sub, map_add, map_mul, map_pow, map_one, map_zero] using
    congrArg (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R)) (ordinary_relation R)

theorem reciprocal_overlap_relation : reciprocalW R ^ 2 +
    (1 + reciprocalZ R + reciprocalZ R ^ 3) * reciprocalW R -
    (reciprocalZ R ^ 4 + reciprocalZ R ^ 5) = 0 := by
  simpa only [reciprocalZ, reciprocalW, map_sub, map_add, map_mul, map_pow, map_one, map_zero] using
    congrArg (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R)) (reciprocal_relation R)

end MazurTransfer.Order13MixedQuadraticOverlapCoordinates
end
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Vas and contributors.
Released under Apache-2.0. Authors: Vasily Ilin.
Adapts the existing reciprocal localization construction to the checked
mixed quadratic equations over arbitrary commutative coefficient rings.
Design boundary: actual homomorphisms in both directions between the two
principal overlap rings. Named downstream consumer: their inverse laws
and the actual dyadic two-chart scheme gluing.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms
open Polynomial MixedQuadraticCoordinateJacobian
open Order13MixedQuadraticJacobianCertificates Order13MixedQuadraticPolynomialEvaluations
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
universe u
variable (R : Type u) [CommRing R]

def ordinaryToReciprocalBase : ordinaryCoordinateRing R →ₐ[R] ReciprocalOverlapRing R :=
  AdjoinRoot.liftAlgHom (equation R (ordinaryH R) (ordinaryF R))
    (aeval (inverseZ R)) (reciprocalW R * inverseZ R ^ 3) (by
    change eval₂ (aeval (inverseZ R)).toRingHom (reciprocalW R * inverseZ R ^ 3)
      (X ^ 2 + C (ordinaryH R) * X - C (ordinaryF R)) = 0
    simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    rw [map_ordinaryH R _, map_ordinaryF R _]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
    exact Order13MixedQuadraticReciprocalRelations.ordinary_relation _ _ _ _
      (reciprocalZ_inverseZ R) (reciprocal_overlap_relation R))

@[simp] theorem ordinaryToReciprocalBase_x : ordinaryToReciprocalBase R (xCoordinate R) = inverseZ R := by
  simp only [ordinaryToReciprocalBase, xCoordinate, AdjoinRoot.liftAlgHom_of, aeval_X]
@[simp] theorem ordinaryToReciprocalBase_y : ordinaryToReciprocalBase R (yCoordinate R) =
    reciprocalW R * inverseZ R ^ 3 := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

def reciprocalToOrdinaryBase : reciprocalCoordinateRing R →ₐ[R] OrdinaryOverlapRing R :=
  AdjoinRoot.liftAlgHom (equation R (reciprocalH R) (reciprocalF R))
    (aeval (inverseX R)) (ordinaryY R * inverseX R ^ 3) (by
    change eval₂ (aeval (inverseX R)).toRingHom (ordinaryY R * inverseX R ^ 3)
      (X ^ 2 + C (reciprocalH R) * X - C (reciprocalF R)) = 0
    simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    rw [map_reciprocalH R _, map_reciprocalF R _]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
    exact Order13MixedQuadraticReciprocalRelations.reciprocal_relation _ _ _ _
      (ordinaryX_inverseX R) (ordinary_overlap_relation R))

@[simp] theorem reciprocalToOrdinaryBase_z : reciprocalToOrdinaryBase R (zCoordinate R) = inverseX R := by
  simp only [reciprocalToOrdinaryBase, zCoordinate, AdjoinRoot.liftAlgHom_of, aeval_X]
@[simp] theorem reciprocalToOrdinaryBase_w : reciprocalToOrdinaryBase R (wCoordinate R) =
    ordinaryY R * inverseX R ^ 3 := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

def ordinaryToReciprocal : OrdinaryOverlapRing R →ₐ[R] ReciprocalOverlapRing R :=
  IsLocalization.Away.liftAlgHom (xCoordinate R) (f := ordinaryToReciprocalBase R)
    (by rw [ordinaryToReciprocalBase_x]; exact inverseZ_isUnit R)
def reciprocalToOrdinary : ReciprocalOverlapRing R →ₐ[R] OrdinaryOverlapRing R :=
  IsLocalization.Away.liftAlgHom (zCoordinate R) (f := reciprocalToOrdinaryBase R)
    (by rw [reciprocalToOrdinaryBase_z]; exact inverseX_isUnit R)

@[simp] theorem ordinaryToReciprocal_algebraMap (a : ordinaryCoordinateRing R) :
    ordinaryToReciprocal R (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) a) =
      ordinaryToReciprocalBase R a := by
  simp only [ordinaryToReciprocal, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] <;> rfl
@[simp] theorem reciprocalToOrdinary_algebraMap (a : reciprocalCoordinateRing R) :
    reciprocalToOrdinary R (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R) a) =
      reciprocalToOrdinaryBase R a := by
  simp only [reciprocalToOrdinary, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] <;> rfl

theorem ordinaryToReciprocal_x : ordinaryToReciprocal R (ordinaryX R) = inverseZ R :=
  (ordinaryToReciprocal_algebraMap R _).trans (ordinaryToReciprocalBase_x R)
theorem ordinaryToReciprocal_y : ordinaryToReciprocal R (ordinaryY R) = reciprocalW R * inverseZ R ^ 3 :=
  (ordinaryToReciprocal_algebraMap R _).trans (ordinaryToReciprocalBase_y R)
theorem reciprocalToOrdinary_z : reciprocalToOrdinary R (reciprocalZ R) = inverseX R :=
  (reciprocalToOrdinary_algebraMap R _).trans (reciprocalToOrdinaryBase_z R)
theorem reciprocalToOrdinary_w : reciprocalToOrdinary R (reciprocalW R) = ordinaryY R * inverseX R ^ 3 :=
  (reciprocalToOrdinary_algebraMap R _).trans (reciprocalToOrdinaryBase_w R)

end MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms
end
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Vas and contributors.
Released under Apache-2.0. Authors: Vasily Ilin.
Adapts the complete inverse-localization method of the existing projective
curve to the integral mixed quadratic transition maps.
Design boundary: a genuine R-algebra equivalence on the entire two overlap
rings. Named downstream consumer: the dyadic two-chart Scheme.GlueData.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticOverlapEquivalence
open Polynomial Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticTransitionHomomorphisms
universe u
variable (R : Type u) [CommRing R]

theorem reciprocalToOrdinary_inverseZ : reciprocalToOrdinary R (inverseZ R) = ordinaryX R := by
  have ht := congrArg (reciprocalToOrdinary R) (reciprocalZ_inverseZ R)
  rw [map_mul, map_one, reciprocalToOrdinary_z] at ht
  exact (left_inv_eq_right_inv (ordinaryX_inverseX R) ht).symm

theorem ordinaryToReciprocal_inverseX : ordinaryToReciprocal R (inverseX R) = reciprocalZ R := by
  have ht := congrArg (ordinaryToReciprocal R) (ordinaryX_inverseX R)
  rw [map_mul, map_one, ordinaryToReciprocal_x] at ht
  exact (left_inv_eq_right_inv (reciprocalZ_inverseZ R) ht).symm

theorem reciprocalToOrdinary_scaledW :
    reciprocalToOrdinary R (reciprocalW R * inverseZ R ^ 3) = ordinaryY R := by
  rw [map_mul, map_pow, reciprocalToOrdinary_w, reciprocalToOrdinary_inverseZ]
  calc
    _ = ordinaryY R * (ordinaryX R * inverseX R) ^ 3 := by ring
    _ = _ := by rw [ordinaryX_inverseX]; simp

theorem ordinaryToReciprocal_scaledY :
    ordinaryToReciprocal R (ordinaryY R * inverseX R ^ 3) = reciprocalW R := by
  rw [map_mul, map_pow, ordinaryToReciprocal_y, ordinaryToReciprocal_inverseX]
  calc
    _ = reciprocalW R * (reciprocalZ R * inverseZ R) ^ 3 := by ring
    _ = _ := by rw [reciprocalZ_inverseZ]; simp

theorem reciprocalToOrdinary_comp_ordinaryToReciprocal :
    (reciprocalToOrdinary R).comp (ordinaryToReciprocal R) = AlgHom.id R (OrdinaryOverlapRing R) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (xCoordinate R))
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change reciprocalToOrdinary R (ordinaryToReciprocal R (ordinaryX R)) = ordinaryX R
    rw [ordinaryToReciprocal_x, reciprocalToOrdinary_inverseZ]
  · change reciprocalToOrdinary R (ordinaryToReciprocal R (ordinaryY R)) = ordinaryY R
    rw [ordinaryToReciprocal_y, reciprocalToOrdinary_scaledW]

theorem ordinaryToReciprocal_comp_reciprocalToOrdinary :
    (ordinaryToReciprocal R).comp (reciprocalToOrdinary R) = AlgHom.id R (ReciprocalOverlapRing R) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (zCoordinate R))
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change ordinaryToReciprocal R (reciprocalToOrdinary R (reciprocalZ R)) = reciprocalZ R
    rw [reciprocalToOrdinary_z, ordinaryToReciprocal_inverseX]
  · change ordinaryToReciprocal R (reciprocalToOrdinary R (reciprocalW R)) = reciprocalW R
    rw [reciprocalToOrdinary_w, ordinaryToReciprocal_scaledY]

def overlapAlgEquiv : OrdinaryOverlapRing R ≃ₐ[R] ReciprocalOverlapRing R :=
  AlgEquiv.ofAlgHom (ordinaryToReciprocal R) (reciprocalToOrdinary R)
    (ordinaryToReciprocal_comp_reciprocalToOrdinary R)
    (reciprocalToOrdinary_comp_ordinaryToReciprocal R)

end MazurTransfer.Order13MixedQuadraticOverlapEquivalence
end
#print axioms MazurTransfer.MixedQuadraticCoordinateJacobian.root_relation
#print axioms MazurTransfer.Order13MixedQuadraticPolynomialEvaluations.map_ordinaryH
#print axioms MazurTransfer.Order13MixedQuadraticPolynomialEvaluations.map_ordinaryF
#print axioms MazurTransfer.Order13MixedQuadraticPolynomialEvaluations.map_reciprocalH
#print axioms MazurTransfer.Order13MixedQuadraticPolynomialEvaluations.map_reciprocalF
#print axioms MazurTransfer.Order13MixedQuadraticReciprocalRelations.reciprocal_relation
#print axioms MazurTransfer.Order13MixedQuadraticReciprocalRelations.ordinary_relation
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.xCoordinate
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.yCoordinate
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.zCoordinate
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.wCoordinate
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.ordinary_relation
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.reciprocal_relation
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.OrdinaryOverlapRing
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.ReciprocalOverlapRing
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.ordinaryX
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.ordinaryY
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.reciprocalZ
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.reciprocalW
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.inverseX
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.inverseZ
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.ordinaryX_inverseX
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.reciprocalZ_inverseZ
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.inverseX_isUnit
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.inverseZ_isUnit
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.ordinary_overlap_relation
#print axioms MazurTransfer.Order13MixedQuadraticOverlapCoordinates.reciprocal_overlap_relation
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocalBase
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocalBase_x
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocalBase_y
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.reciprocalToOrdinaryBase
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.reciprocalToOrdinaryBase_z
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.reciprocalToOrdinaryBase_w
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocal
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.reciprocalToOrdinary
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocal_algebraMap
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.reciprocalToOrdinary_algebraMap
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocal_x
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocal_y
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.reciprocalToOrdinary_z
#print axioms MazurTransfer.Order13MixedQuadraticTransitionHomomorphisms.reciprocalToOrdinary_w
#print axioms MazurTransfer.Order13MixedQuadraticOverlapEquivalence.reciprocalToOrdinary_inverseZ
#print axioms MazurTransfer.Order13MixedQuadraticOverlapEquivalence.ordinaryToReciprocal_inverseX
#print axioms MazurTransfer.Order13MixedQuadraticOverlapEquivalence.reciprocalToOrdinary_scaledW
#print axioms MazurTransfer.Order13MixedQuadraticOverlapEquivalence.ordinaryToReciprocal_scaledY
#print axioms MazurTransfer.Order13MixedQuadraticOverlapEquivalence.reciprocalToOrdinary_comp_ordinaryToReciprocal
#print axioms MazurTransfer.Order13MixedQuadraticOverlapEquivalence.ordinaryToReciprocal_comp_reciprocalToOrdinary
#print axioms MazurTransfer.Order13MixedQuadraticOverlapEquivalence.overlapAlgEquiv


