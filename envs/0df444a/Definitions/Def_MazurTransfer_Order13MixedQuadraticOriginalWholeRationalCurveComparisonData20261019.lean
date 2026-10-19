-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeRationalCurveComparisonData20261019
-- name    : MazurTransfer_Order13MixedQuadraticOriginalWholeRationalCurveComparisonData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T05:14:39.202438+00:00
-- url     : https://prove2.me/theorems/a7a4298e-a2e2-44ad-b244-341b694ea1b1
-- title:
--   Original whole mixed quadratic rational-curve comparison
-- statement:
--   The original whole scheme isomorphism between the mixed quadratic model and the square model when a chosen coefficient c satisfies 2c=1, its rational specialization, compatibility with the whole base morphisms and both original rational chart isomorphisms. All original public and private constructor types and whole nonproof values are independently checked at default heartbeats. The named downstream consumer is the actual dyadic whole generic-fibre and Picard comparison.
-- source:
--   MazurTheorem original mixed quadratic integral charts, overlap and gluing, by Vasily Ilin and contributors; Apache-2.0. Original attribution retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: extend an algebra equivalence preserving a chosen element
to its entire principal localizations. Named downstream consumer: the
ordinary and reciprocal completing-square overlap comparisons.
-/
noncomputable section
namespace MazurTransfer.MixedQuadraticOriginalLocalizationAwayEquivalence20261019
universe u v w
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
  {B : Type w} [CommRing B] [Algebra R B]
variable (e : A ≃ₐ[R] B) (a : A) (b : B) (hab : e a = b)

def forward : Localization.Away a →ₐ[R] Localization.Away b :=
  IsLocalization.Away.liftAlgHom a
    (f := (IsScalarTower.toAlgHom R B (Localization.Away b)).comp e.toAlgHom)
    (by
      change IsUnit (algebraMap B (Localization.Away b) (e a))
      rw [hab]
      exact IsLocalization.Away.algebraMap_isUnit b)

@[simp] theorem forward_algebraMap (x : A) :
    forward e a b hab (algebraMap A (Localization.Away a) x) =
      algebraMap B (Localization.Away b) (e x) := by
  simp only [forward, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
  rfl

include hab in
theorem reverse_element : e.symm b = a := by rw [← hab, e.symm_apply_apply]

def equiv : Localization.Away a ≃ₐ[R] Localization.Away b :=
  AlgEquiv.ofAlgHom (forward e a b hab) (forward e.symm b a (reverse_element e a b hab))
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers b)
      ext x
      change forward e a b hab (forward e.symm b a (reverse_element e a b hab)
        (algebraMap B (Localization.Away b) x)) = algebraMap B (Localization.Away b) x
      simp only [forward_algebraMap, e.apply_symm_apply])
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers a)
      ext x
      change forward e.symm b a (reverse_element e a b hab) (forward e a b hab
        (algebraMap A (Localization.Away a) x)) = algebraMap A (Localization.Away a) x
      simp only [forward_algebraMap, e.symm_apply_apply])

@[simp] theorem equiv_algebraMap (x : A) :
    equiv e a b hab (algebraMap A (Localization.Away a) x) =
      algebraMap B (Localization.Away b) (e x) := forward_algebraMap e a b hab x

end MazurTransfer.MixedQuadraticOriginalLocalizationAwayEquivalence20261019
#print axioms MazurTransfer.MixedQuadraticOriginalLocalizationAwayEquivalence20261019.equiv

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the complete checked two-chart descent proof of MazurTheorem at
54d43d8dda8a6fcf069cc02a815f850d762c5c0c to an arbitrary target scheme.
Design boundary: the actual universal gluing morphism for compatible chart
maps. Named downstream consumer: the genuine change-of-base morphism of the
literal integral order-thirteen curve, with compatibility proved separately.
-/
noncomputable section
namespace MazurTransfer.MixedQuadraticOriginalSquareCurveMaps20261019
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [CommRing K]

private theorem ordinary_ne_reciprocal : (Chart.ordinary : Chart.{u}) ≠ Chart.reciprocal := by
  intro h
  cases h

private theorem reciprocal_ne_ordinary : (Chart.reciprocal : Chart.{u}) ≠ Chart.ordinary := by
  intro h
  cases h

def desc {Y : Scheme.{u}} (δ : ∀ i : Chart.{u}, chartScheme K i ⟶ Y)
    (hδ : ∀ (i j : Chart.{u}) (h : i ≠ j),
      overlapInclusion K i j h ≫ δ i =
        overlapTransition K i j h ≫ overlapInclusion K j i h.symm ≫ δ j) :
    curveScheme K ⟶ Y := by
    letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
    exact Limits.Multicoequalizer.desc (glueData K).toGlueData.diagram
      Y δ (by
      rintro ⟨i, j⟩
      simp only [CategoryTheory.GlueData.diagram_fst,
        CategoryTheory.GlueData.diagram_snd]
      rcases i with (_ | _) <;> rcases j with (_ | _)
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f',
          Limits.MultispanShape.prod]
        simp
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f',
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact hδ _ _
          ordinary_ne_reciprocal
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f',
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact hδ _ _
          reciprocal_ne_ordinary
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f',
          Limits.MultispanShape.prod]
        simp)

theorem chartMap_desc {Y : Scheme.{u}} (δ : ∀ i : Chart.{u}, chartScheme K i ⟶ Y)
    (hδ : ∀ (i j : Chart.{u}) (h : i ≠ j),
      overlapInclusion K i j h ≫ δ i =
        overlapTransition K i j h ≫ overlapInclusion K j i h.symm ≫ δ j)
    (i : Chart.{u}) :
    (glueData K).ι i ≫ desc K δ hδ = δ i := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  unfold desc
  apply Multicoequalizer.π_desc

end MazurTransfer.MixedQuadraticOriginalSquareCurveMaps20261019

#print axioms MazurTransfer.MixedQuadraticOriginalSquareCurveMaps20261019.desc
#print axioms MazurTransfer.MixedQuadraticOriginalSquareCurveMaps20261019.chartMap_desc

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: generator formulas for the actual completing-square chart
isomorphisms. Named downstream consumer: their full overlap compatibility
and the whole-curve comparison with the existing rational model.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticSquareComparisonGenerators
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticRationalChartComparison
open Order13MixedQuadraticJacobianCertificates MixedQuadraticCompletingSquare
universe u
variable (R : Type u) [CommRing R] (c : Polynomial R) (hc : 2 * c = 1)

def ordinaryEquiv : MazurTorsion.XOneThirteenAffineCurve.CoordinateRing R ≃ₐ[R] ordinaryCoordinateRing R :=
  (ordinaryChartEquiv R c hc).symm.restrictScalars R

def reciprocalEquiv : MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalRing R ≃ₐ[R] reciprocalCoordinateRing R :=
  (reciprocalChartEquiv R c hc).symm.restrictScalars R

@[simp] theorem ordinaryEquiv_x :
    ordinaryEquiv R c hc (MazurTorsion.XOneThirteenAffineCurve.xCoordinate R) = Order13MixedQuadraticOverlapCoordinates.xCoordinate R := by
  exact (ordinaryChartEquiv R c hc).symm.commutes X

@[simp] theorem reciprocalEquiv_z :
    reciprocalEquiv R c hc (MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate R) = Order13MixedQuadraticOverlapCoordinates.zCoordinate R := by
  exact (reciprocalChartEquiv R c hc).symm.commutes X

private theorem completed_root (A : Type u) [CommRing A] (h f c : A) (hc : 2 * c = 1)
    (g : Polynomial A) (hg : squarePolynomial A h f = g) :
    ((completingSquareEquiv A h f c hc).trans (AdjoinRoot.algEquivOfEq A _ g hg)).symm
      (AdjoinRoot.root g) =
        2 * AdjoinRoot.root (mixedPolynomial A h f) + AdjoinRoot.of (mixedPolynomial A h f) h := by
  rw [AlgEquiv.symm_trans_apply, AdjoinRoot.algEquivOfEq_symm, AdjoinRoot.algEquivOfEq_root]
  exact fromSquare_root A h f

@[simp] theorem ordinaryEquiv_y :
    ordinaryEquiv R c hc (MazurTorsion.XOneThirteenAffineCurve.yCoordinate R) =
      2 * Order13MixedQuadraticOverlapCoordinates.yCoordinate R + Order13MixedQuadraticOverlapCoordinates.xCoordinate R ^ 3 + Order13MixedQuadraticOverlapCoordinates.xCoordinate R ^ 2 + 1 := by
  have ht : ordinaryEquiv R c hc (MazurTorsion.XOneThirteenAffineCurve.yCoordinate R) =
      2 * Order13MixedQuadraticOverlapCoordinates.yCoordinate R +
        AdjoinRoot.of (MixedQuadraticCoordinateJacobian.equation R (ordinaryH R) (ordinaryF R)) (ordinaryH R) :=
    completed_root (Polynomial R) (ordinaryH R) (ordinaryF R) c hc
      (MazurTorsion.XOneThirteenAffineCurve.affineEquation R) (by
        unfold squarePolynomial
        rw [ordinary_discriminant_identity]
        rfl)
  rw [ht]
  rw [Order13MixedQuadraticPolynomialEvaluations.map_ordinaryH R _]
  change 2 * Order13MixedQuadraticOverlapCoordinates.yCoordinate R +
      (Order13MixedQuadraticOverlapCoordinates.xCoordinate R ^ 3 +
        Order13MixedQuadraticOverlapCoordinates.xCoordinate R ^ 2 + 1) = _
  ring

@[simp] theorem reciprocalEquiv_w :
    reciprocalEquiv R c hc (MazurTorsion.XOneThirteenProjectiveCurve.wCoordinate R) =
      2 * Order13MixedQuadraticOverlapCoordinates.wCoordinate R + 1 + Order13MixedQuadraticOverlapCoordinates.zCoordinate R + Order13MixedQuadraticOverlapCoordinates.zCoordinate R ^ 3 := by
  have ht : reciprocalEquiv R c hc (MazurTorsion.XOneThirteenProjectiveCurve.wCoordinate R) =
      2 * Order13MixedQuadraticOverlapCoordinates.wCoordinate R +
        AdjoinRoot.of (MixedQuadraticCoordinateJacobian.equation R (reciprocalH R) (reciprocalF R)) (reciprocalH R) :=
    completed_root (Polynomial R) (reciprocalH R) (reciprocalF R) c hc
      (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalEquation R) (by
        unfold squarePolynomial
        rw [reciprocal_discriminant_identity]
        rfl)
  rw [ht]
  rw [Order13MixedQuadraticPolynomialEvaluations.map_reciprocalH R _]
  change 2 * Order13MixedQuadraticOverlapCoordinates.wCoordinate R +
      (1 + Order13MixedQuadraticOverlapCoordinates.zCoordinate R +
        Order13MixedQuadraticOverlapCoordinates.zCoordinate R ^ 3) = _
  ring

end MazurTransfer.Order13MixedQuadraticSquareComparisonGenerators
#print axioms MazurTransfer.Order13MixedQuadraticSquareComparisonGenerators.ordinaryEquiv_y
#print axioms MazurTransfer.Order13MixedQuadraticSquareComparisonGenerators.reciprocalEquiv_w

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: completing-square isomorphisms on the FULL ordinary and
reciprocal principal localizations and their actual transition square.
Named downstream consumer: the whole rational glued-curve isomorphism.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticSquareOverlapComparison
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticSquareComparisonGenerators
universe u
variable (R : Type u) [CommRing R] (c : Polynomial R) (hc : 2 * c = 1)

def ordinaryOverlapEquiv : MazurTorsion.XOneThirteenProjectiveCurve.OrdinaryOverlapRing R ≃ₐ[R] Order13MixedQuadraticOverlapCoordinates.OrdinaryOverlapRing R :=
  MazurTransfer.MixedQuadraticOriginalLocalizationAwayEquivalence20261019.equiv (ordinaryEquiv R c hc)
    (MazurTorsion.XOneThirteenAffineCurve.xCoordinate R) (Order13MixedQuadraticOverlapCoordinates.xCoordinate R) (ordinaryEquiv_x R c hc)

def reciprocalOverlapEquiv : MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalOverlapRing R ≃ₐ[R] Order13MixedQuadraticOverlapCoordinates.ReciprocalOverlapRing R :=
  MazurTransfer.MixedQuadraticOriginalLocalizationAwayEquivalence20261019.equiv (reciprocalEquiv R c hc)
    (MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate R) (Order13MixedQuadraticOverlapCoordinates.zCoordinate R) (reciprocalEquiv_z R c hc)

@[simp] theorem ordinaryOverlapEquiv_algebraMap (a : MazurTorsion.XOneThirteenAffineCurve.CoordinateRing R) :
    ordinaryOverlapEquiv R c hc (algebraMap _ (MazurTorsion.XOneThirteenProjectiveCurve.OrdinaryOverlapRing R) a) =
      algebraMap _ (Order13MixedQuadraticOverlapCoordinates.OrdinaryOverlapRing R) (ordinaryEquiv R c hc a) :=
  MazurTransfer.MixedQuadraticOriginalLocalizationAwayEquivalence20261019.equiv_algebraMap _ _ _ _ a

@[simp] theorem reciprocalOverlapEquiv_algebraMap (a : MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalRing R) :
    reciprocalOverlapEquiv R c hc (algebraMap _ (MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalOverlapRing R) a) =
      algebraMap _ (Order13MixedQuadraticOverlapCoordinates.ReciprocalOverlapRing R) (reciprocalEquiv R c hc a) :=
  MazurTransfer.MixedQuadraticOriginalLocalizationAwayEquivalence20261019.equiv_algebraMap _ _ _ _ a

@[simp] theorem ordinaryOverlapEquiv_x :
    ordinaryOverlapEquiv R c hc
      (algebraMap _ (MazurTorsion.XOneThirteenProjectiveCurve.OrdinaryOverlapRing R) (MazurTorsion.XOneThirteenAffineCurve.xCoordinate R)) = Order13MixedQuadraticOverlapCoordinates.ordinaryX R := by
  rw [ordinaryOverlapEquiv_algebraMap, ordinaryEquiv_x]
  rfl

@[simp] theorem ordinaryOverlapEquiv_y :
    ordinaryOverlapEquiv R c hc
      (algebraMap _ (MazurTorsion.XOneThirteenProjectiveCurve.OrdinaryOverlapRing R) (MazurTorsion.XOneThirteenAffineCurve.yCoordinate R)) =
      2 * Order13MixedQuadraticOverlapCoordinates.ordinaryY R + Order13MixedQuadraticOverlapCoordinates.ordinaryX R ^ 3 + Order13MixedQuadraticOverlapCoordinates.ordinaryX R ^ 2 + 1 := by
  rw [ordinaryOverlapEquiv_algebraMap, ordinaryEquiv_y]
  simp only [map_add, map_mul, map_ofNat, map_pow, map_one]
  rfl

@[simp] theorem reciprocalOverlapEquiv_z :
    reciprocalOverlapEquiv R c hc
      (algebraMap _ (MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalOverlapRing R) (MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate R)) = Order13MixedQuadraticOverlapCoordinates.reciprocalZ R := by
  rw [reciprocalOverlapEquiv_algebraMap, reciprocalEquiv_z]
  rfl

@[simp] theorem reciprocalOverlapEquiv_w :
    reciprocalOverlapEquiv R c hc
      (algebraMap _ (MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalOverlapRing R) (MazurTorsion.XOneThirteenProjectiveCurve.wCoordinate R)) =
      2 * Order13MixedQuadraticOverlapCoordinates.reciprocalW R + 1 + Order13MixedQuadraticOverlapCoordinates.reciprocalZ R + Order13MixedQuadraticOverlapCoordinates.reciprocalZ R ^ 3 := by
  rw [reciprocalOverlapEquiv_algebraMap, reciprocalEquiv_w]
  simp only [map_add, map_mul, map_ofNat, map_pow, map_one]
  rfl

@[simp] theorem ordinaryOverlapEquiv_inverseX :
    ordinaryOverlapEquiv R c hc (IsLocalization.Away.invSelf (MazurTorsion.XOneThirteenAffineCurve.xCoordinate R)) = Order13MixedQuadraticOverlapCoordinates.inverseX R := by
  have ht := congrArg (ordinaryOverlapEquiv R c hc)
    (IsLocalization.Away.mul_invSelf (S := MazurTorsion.XOneThirteenProjectiveCurve.OrdinaryOverlapRing R) (MazurTorsion.XOneThirteenAffineCurve.xCoordinate R))
  rw [map_mul, map_one, ordinaryOverlapEquiv_x] at ht
  exact left_inv_eq_right_inv (by simpa [mul_comm] using ht) (Order13MixedQuadraticOverlapCoordinates.ordinaryX_inverseX R)

@[simp] theorem reciprocalOverlapEquiv_inverseZ :
    reciprocalOverlapEquiv R c hc (IsLocalization.Away.invSelf (MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate R)) = Order13MixedQuadraticOverlapCoordinates.inverseZ R := by
  have ht := congrArg (reciprocalOverlapEquiv R c hc)
    (IsLocalization.Away.mul_invSelf (S := MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalOverlapRing R) (MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate R))
  rw [map_mul, map_one, reciprocalOverlapEquiv_z] at ht
  exact left_inv_eq_right_inv (by simpa [mul_comm] using ht) (Order13MixedQuadraticOverlapCoordinates.reciprocalZ_inverseZ R)

theorem shift_reciprocal_identity (A : Type u) [CommRing A] (x z w : A) (hxz : x * z = 1) :
    2 * (w * x ^ 3) + x ^ 3 + x ^ 2 + 1 = (2 * w + 1 + z + z ^ 3) * x ^ 3 := by
  have hp : (x * z) ^ 3 = 1 := by rw [hxz, one_pow]
  linear_combination -x ^ 2 * hxz - hp

theorem transition_compatible :
    (Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocal R).comp (ordinaryOverlapEquiv R c hc).toAlgHom =
      (reciprocalOverlapEquiv R c hc).toAlgHom.comp (MazurTorsion.XOneThirteenProjectiveCurve.ordinaryToReciprocal R) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (MazurTorsion.XOneThirteenAffineCurve.xCoordinate R))
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocal R (ordinaryOverlapEquiv R c hc
      (algebraMap _ (MazurTorsion.XOneThirteenProjectiveCurve.OrdinaryOverlapRing R) (MazurTorsion.XOneThirteenAffineCurve.xCoordinate R))) =
      reciprocalOverlapEquiv R c hc (MazurTorsion.XOneThirteenProjectiveCurve.ordinaryToReciprocal R
        (algebraMap _ (MazurTorsion.XOneThirteenProjectiveCurve.OrdinaryOverlapRing R) (MazurTorsion.XOneThirteenAffineCurve.xCoordinate R)))
    rw [ordinaryOverlapEquiv_x, Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocal_x,
      MazurTorsion.XOneThirteenProjectiveCurve.ordinaryToReciprocal_algebraMap, MazurTorsion.XOneThirteenProjectiveCurve.ordinaryToReciprocalBase_x]
    exact (reciprocalOverlapEquiv_inverseZ R c hc).symm
  · change Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocal R (ordinaryOverlapEquiv R c hc
      (algebraMap _ (MazurTorsion.XOneThirteenProjectiveCurve.OrdinaryOverlapRing R) (MazurTorsion.XOneThirteenAffineCurve.yCoordinate R))) =
      reciprocalOverlapEquiv R c hc (MazurTorsion.XOneThirteenProjectiveCurve.ordinaryToReciprocal R
        (algebraMap _ (MazurTorsion.XOneThirteenProjectiveCurve.OrdinaryOverlapRing R) (MazurTorsion.XOneThirteenAffineCurve.yCoordinate R)))
    rw [ordinaryOverlapEquiv_y, MazurTorsion.XOneThirteenProjectiveCurve.ordinaryToReciprocal_algebraMap,
      MazurTorsion.XOneThirteenProjectiveCurve.ordinaryToReciprocalBase_y]
    change Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocal R
      (2 * Order13MixedQuadraticOverlapCoordinates.ordinaryY R + Order13MixedQuadraticOverlapCoordinates.ordinaryX R ^ 3 + Order13MixedQuadraticOverlapCoordinates.ordinaryX R ^ 2 + 1) =
        reciprocalOverlapEquiv R c hc
          (algebraMap _ (MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalOverlapRing R) (MazurTorsion.XOneThirteenProjectiveCurve.wCoordinate R) *
            IsLocalization.Away.invSelf (MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate R) ^ 3)
    rw [map_mul, map_pow, reciprocalOverlapEquiv_w, reciprocalOverlapEquiv_inverseZ]
    simp only [map_add, map_mul, map_ofNat, map_pow, map_one,
      Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocal_y, Order13MixedQuadraticTransitionHomomorphisms.ordinaryToReciprocal_x]
    exact shift_reciprocal_identity _ _ _ _ (by simpa [mul_comm] using Order13MixedQuadraticOverlapCoordinates.reciprocalZ_inverseZ R)

end MazurTransfer.Order13MixedQuadraticSquareOverlapComparison
#print axioms MazurTransfer.Order13MixedQuadraticSquareOverlapComparison.transition_compatible

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual completing-square isomorphisms of both chart and
overlap schemes, with inclusion and transition squares in both directions.
Named downstream consumer: gluing a whole-curve isomorphism.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticSquareTransitionSquares
open Polynomial CategoryTheory AlgebraicGeometry
open Order13MixedQuadraticSquareComparisonGenerators Order13MixedQuadraticSquareOverlapComparison
universe u
variable (R : Type u) [CommRing R] (c : Polynomial R) (hc : 2 * c = 1)

private theorem reverse_compatibility {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (s : A ≃ₐ[R] B) (t : C ≃ₐ[R] D) (e : A ≃ₐ[R] C) (f : B ≃ₐ[R] D)
    (h : ∀ a, t (e a) = f (s a)) (b : B) : t.symm (f b) = e (s.symm b) := by
  apply t.injective
  rw [t.apply_symm_apply, h, s.apply_symm_apply]

theorem reciprocal_transition_compatible :
    (Order13MixedQuadraticTransitionHomomorphisms.reciprocalToOrdinary R).comp (reciprocalOverlapEquiv R c hc).toAlgHom =
      (ordinaryOverlapEquiv R c hc).toAlgHom.comp (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalToOrdinary R) := by
  apply DFunLike.ext
  intro b
  exact reverse_compatibility R (MazurTorsion.XOneThirteenProjectiveCurve.overlapAlgEquiv R)
    (Order13MixedQuadraticOverlapEquivalence.overlapAlgEquiv R)
    (ordinaryOverlapEquiv R c hc) (reciprocalOverlapEquiv R c hc)
    (fun a => DFunLike.congr_fun (transition_compatible R c hc) a) b

def ordinaryIso : Order13DyadicMixedQuadraticCharts.ordinaryScheme R ≅ MazurTorsion.XOneThirteenAffineCurve.scheme R :=
  Scheme.Spec.mapIso (ordinaryEquiv R c hc).toRingEquiv.toCommRingCatIso.op

def reciprocalIso : Order13DyadicMixedQuadraticCharts.reciprocalScheme R ≅ MazurTorsion.XOneThirteenProjectiveCurve.reciprocalScheme R :=
  Scheme.Spec.mapIso (reciprocalEquiv R c hc).toRingEquiv.toCommRingCatIso.op

def ordinaryOverlapIso : Spec (.of (Order13MixedQuadraticOverlapCoordinates.OrdinaryOverlapRing R)) ≅ Spec (.of (MazurTorsion.XOneThirteenProjectiveCurve.OrdinaryOverlapRing R)) :=
  Scheme.Spec.mapIso (ordinaryOverlapEquiv R c hc).toRingEquiv.toCommRingCatIso.op

def reciprocalOverlapIso : Spec (.of (Order13MixedQuadraticOverlapCoordinates.ReciprocalOverlapRing R)) ≅ Spec (.of (MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalOverlapRing R)) :=
  Scheme.Spec.mapIso (reciprocalOverlapEquiv R c hc).toRingEquiv.toCommRingCatIso.op

abbrev newOrdInclusion : Spec (.of (Order13MixedQuadraticOverlapCoordinates.OrdinaryOverlapRing R)) ⟶ Order13DyadicMixedQuadraticCharts.ordinaryScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing R) (Order13MixedQuadraticOverlapCoordinates.OrdinaryOverlapRing R)))
abbrev newRecInclusion : Spec (.of (Order13MixedQuadraticOverlapCoordinates.ReciprocalOverlapRing R)) ⟶ Order13DyadicMixedQuadraticCharts.reciprocalScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing R) (Order13MixedQuadraticOverlapCoordinates.ReciprocalOverlapRing R)))
abbrev oldOrdInclusion : Spec (.of (MazurTorsion.XOneThirteenProjectiveCurve.OrdinaryOverlapRing R)) ⟶ MazurTorsion.XOneThirteenAffineCurve.scheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (MazurTorsion.XOneThirteenAffineCurve.CoordinateRing R) (MazurTorsion.XOneThirteenProjectiveCurve.OrdinaryOverlapRing R)))
abbrev oldRecInclusion : Spec (.of (MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalOverlapRing R)) ⟶ MazurTorsion.XOneThirteenProjectiveCurve.reciprocalScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalRing R) (MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalOverlapRing R)))

@[reassoc] theorem ordinary_inclusion_square :
    newOrdInclusion R ≫ (ordinaryIso R c hc).hom =
      (ordinaryOverlapIso R c hc).hom ≫ oldOrdInclusion R := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply DFunLike.ext
  intro a
  exact (ordinaryOverlapEquiv_algebraMap R c hc a).symm

@[reassoc] theorem reciprocal_inclusion_square :
    newRecInclusion R ≫ (reciprocalIso R c hc).hom =
      (reciprocalOverlapIso R c hc).hom ≫ oldRecInclusion R := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply DFunLike.ext
  intro a
  exact (reciprocalOverlapEquiv_algebraMap R c hc a).symm

@[reassoc] theorem ordinary_transition_square :
    (Order13MixedQuadraticGluedCurve.overlapSchemeIso R).hom ≫ (reciprocalOverlapIso R c hc).hom =
      (ordinaryOverlapIso R c hc).hom ≫ (MazurTorsion.XOneThirteenProjectiveCurve.overlapSchemeIso R).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply DFunLike.ext
  intro a
  exact DFunLike.congr_fun (reciprocal_transition_compatible R c hc) a

@[reassoc] theorem reciprocal_transition_square :
    (Order13MixedQuadraticGluedCurve.overlapSchemeIso R).inv ≫ (ordinaryOverlapIso R c hc).hom =
      (reciprocalOverlapIso R c hc).hom ≫ (MazurTorsion.XOneThirteenProjectiveCurve.overlapSchemeIso R).inv := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply DFunLike.ext
  intro a
  exact DFunLike.congr_fun (transition_compatible R c hc) a

end MazurTransfer.Order13MixedQuadraticSquareTransitionSquares
#print axioms MazurTransfer.Order13MixedQuadraticSquareTransitionSquares.ordinary_transition_square
#print axioms MazurTransfer.Order13MixedQuadraticSquareTransitionSquares.ordinary_inclusion_square

end
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Vas and contributors.
Released under Apache-2.0. Authors: Vasily Ilin.
Uses the actual original two-chart gluing at the pinned MazurTheorem source.
Design boundary: a whole-curve isomorphism from the mixed quadratic model
to the SAME existing square model when two is invertible. Named downstream
consumer: the whole dyadic generic-fibre comparison.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticWholeCurveComparison
open Polynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Order13MixedQuadraticSquareTransitionSquares
universe u
variable (R : Type u) [CommRing R] (c : Polynomial R) (hc : 2 * c = 1)

theorem old_glue : oldOrdInclusion R ≫ MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartMap R =
    (MazurTorsion.XOneThirteenProjectiveCurve.overlapSchemeIso R).hom ≫ oldRecInclusion R ≫ MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartMap R := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (MazurTorsion.XOneThirteenProjectiveCurve.glueData R)
  exact MazurTransfer.MixedQuadraticGlueDataOriginalDistinctCompatibility20261019.relation
    (MazurTorsion.XOneThirteenProjectiveCurve.categoricalGlueData R) MazurTorsion.XOneThirteenProjectiveCurve.Chart.ordinary
      MazurTorsion.XOneThirteenProjectiveCurve.Chart.reciprocal (by intro h; cases h)

theorem new_glue : newOrdInclusion R ≫ Order13MixedQuadraticGluedCurve.ordinaryChartMap R =
    (Order13MixedQuadraticGluedCurve.overlapSchemeIso R).hom ≫ newRecInclusion R ≫ Order13MixedQuadraticGluedCurve.reciprocalChartMap R := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (Order13MixedQuadraticGluedCurve.glueData R)
  exact MazurTransfer.MixedQuadraticGlueDataOriginalDistinctCompatibility20261019.relation
    (Order13MixedQuadraticGluedCurve.categoricalGlueData R) Order13MixedQuadraticGluedCurve.Chart.ordinary
      Order13MixedQuadraticGluedCurve.Chart.reciprocal (by intro h; cases h)

private theorem inverse_square {A B C D : Scheme.{u}} (e : A ≅ B) (f : C ≅ D)
    (x : A ⟶ C) (y : B ⟶ D) (h : x ≫ f.hom = e.hom ≫ y) :
    y ≫ f.inv = e.inv ≫ x := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact h.symm

private theorem reverse_glue {A B X : Scheme.{u}} (t : A ≅ B) (f : A ⟶ X) (g : B ⟶ X)
    (h : f = t.hom ≫ g) : g = t.inv ≫ f := by
  rw [Iso.eq_inv_comp]
  exact h.symm

theorem forward_ordinary_compatible :
    newOrdInclusion R ≫ ((ordinaryIso R c hc).hom ≫ MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartMap R) =
      (Order13MixedQuadraticGluedCurve.overlapSchemeIso R).hom ≫ newRecInclusion R ≫
        (reciprocalIso R c hc).hom ≫ MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartMap R := by
  rw [← Category.assoc, ordinary_inclusion_square, Category.assoc, old_glue]
  rw [← Category.assoc, ← ordinary_transition_square]
  simp only [Category.assoc]
  rw [← reciprocal_inclusion_square_assoc]

def forwardChart : ∀ i : Order13MixedQuadraticGluedCurve.Chart, Order13MixedQuadraticGluedCurve.chartScheme R i ⟶ MazurTorsion.XOneThirteenProjectiveCurve.curveScheme R
  | .ordinary => (ordinaryIso R c hc).hom ≫ MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartMap R
  | .reciprocal => (reciprocalIso R c hc).hom ≫ MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartMap R

theorem forward_compatible (i j : Order13MixedQuadraticGluedCurve.Chart) (h : i ≠ j) :
    Order13MixedQuadraticGluedCurve.overlapInclusion R i j h ≫ forwardChart R c hc i =
      Order13MixedQuadraticGluedCurve.overlapTransition R i j h ≫ Order13MixedQuadraticGluedCurve.overlapInclusion R j i h.symm ≫ forwardChart R c hc j := by
  cases i <;> cases j
  · exact (h rfl).elim
  · exact forward_ordinary_compatible R c hc
  · exact reverse_glue (Order13MixedQuadraticGluedCurve.overlapSchemeIso R) _ _ (forward_ordinary_compatible R c hc)
  · exact (h rfl).elim

def forward : Order13MixedQuadraticGluedCurve.curveScheme R ⟶ MazurTorsion.XOneThirteenProjectiveCurve.curveScheme R :=
  Order13MixedQuadraticGluedCurveMaps.desc R (forwardChart R c hc) (forward_compatible R c hc)

@[reassoc] theorem ordinary_forward : Order13MixedQuadraticGluedCurve.ordinaryChartMap R ≫ forward R c hc =
    (ordinaryIso R c hc).hom ≫ MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartMap R :=
  Order13MixedQuadraticGluedCurveMaps.chartMap_desc R _ _ Order13MixedQuadraticGluedCurve.Chart.ordinary

@[reassoc] theorem reciprocal_forward : Order13MixedQuadraticGluedCurve.reciprocalChartMap R ≫ forward R c hc =
    (reciprocalIso R c hc).hom ≫ MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartMap R :=
  Order13MixedQuadraticGluedCurveMaps.chartMap_desc R _ _ Order13MixedQuadraticGluedCurve.Chart.reciprocal


@[reassoc] theorem ordinary_inverse_inclusion_square :
    oldOrdInclusion R ≫ (ordinaryIso R c hc).inv =
      (ordinaryOverlapIso R c hc).inv ≫ newOrdInclusion R :=
  inverse_square (ordinaryOverlapIso R c hc) (ordinaryIso R c hc) _ _
    (ordinary_inclusion_square R c hc)

@[reassoc] theorem reciprocal_inverse_inclusion_square :
    oldRecInclusion R ≫ (reciprocalIso R c hc).inv =
      (reciprocalOverlapIso R c hc).inv ≫ newRecInclusion R :=
  inverse_square (reciprocalOverlapIso R c hc) (reciprocalIso R c hc) _ _
    (reciprocal_inclusion_square R c hc)

@[reassoc] theorem ordinary_inverse_transition_square :
    (MazurTorsion.XOneThirteenProjectiveCurve.overlapSchemeIso R).hom ≫ (reciprocalOverlapIso R c hc).inv =
      (ordinaryOverlapIso R c hc).inv ≫ (Order13MixedQuadraticGluedCurve.overlapSchemeIso R).hom :=
  inverse_square (ordinaryOverlapIso R c hc) (reciprocalOverlapIso R c hc) _ _
    (ordinary_transition_square R c hc)

theorem backward_ordinary_compatible :
    oldOrdInclusion R ≫ ((ordinaryIso R c hc).inv ≫ Order13MixedQuadraticGluedCurve.ordinaryChartMap R) =
      (MazurTorsion.XOneThirteenProjectiveCurve.overlapSchemeIso R).hom ≫ oldRecInclusion R ≫
        (reciprocalIso R c hc).inv ≫ Order13MixedQuadraticGluedCurve.reciprocalChartMap R := by
  rw [← Category.assoc, ordinary_inverse_inclusion_square, Category.assoc, new_glue]
  rw [← Category.assoc, ← ordinary_inverse_transition_square]
  simp only [Category.assoc]
  rw [← reciprocal_inverse_inclusion_square_assoc]

def backwardChart : ∀ i : MazurTorsion.XOneThirteenProjectiveCurve.Chart, MazurTorsion.XOneThirteenProjectiveCurve.chartScheme R i ⟶ Order13MixedQuadraticGluedCurve.curveScheme R
  | .ordinary => (ordinaryIso R c hc).inv ≫ Order13MixedQuadraticGluedCurve.ordinaryChartMap R
  | .reciprocal => (reciprocalIso R c hc).inv ≫ Order13MixedQuadraticGluedCurve.reciprocalChartMap R

theorem backward_compatible (i j : MazurTorsion.XOneThirteenProjectiveCurve.Chart) (h : i ≠ j) :
    MazurTorsion.XOneThirteenProjectiveCurve.overlapInclusion R i j h ≫ backwardChart R c hc i =
      MazurTorsion.XOneThirteenProjectiveCurve.overlapTransition R i j h ≫ MazurTorsion.XOneThirteenProjectiveCurve.overlapInclusion R j i h.symm ≫ backwardChart R c hc j := by
  cases i <;> cases j
  · exact (h rfl).elim
  · exact backward_ordinary_compatible R c hc
  · exact reverse_glue (MazurTorsion.XOneThirteenProjectiveCurve.overlapSchemeIso R) _ _ (backward_ordinary_compatible R c hc)
  · exact (h rfl).elim

def backward : MazurTorsion.XOneThirteenProjectiveCurve.curveScheme R ⟶ Order13MixedQuadraticGluedCurve.curveScheme R :=
  MazurTransfer.MixedQuadraticOriginalSquareCurveMaps20261019.desc R (backwardChart R c hc) (backward_compatible R c hc)

@[reassoc] theorem ordinary_backward : MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartMap R ≫ backward R c hc =
    (ordinaryIso R c hc).inv ≫ Order13MixedQuadraticGluedCurve.ordinaryChartMap R :=
  MazurTransfer.MixedQuadraticOriginalSquareCurveMaps20261019.chartMap_desc R _ _ MazurTorsion.XOneThirteenProjectiveCurve.Chart.ordinary

@[reassoc] theorem reciprocal_backward : MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartMap R ≫ backward R c hc =
    (reciprocalIso R c hc).inv ≫ Order13MixedQuadraticGluedCurve.reciprocalChartMap R :=
  MazurTransfer.MixedQuadraticOriginalSquareCurveMaps20261019.chartMap_desc R _ _ MazurTorsion.XOneThirteenProjectiveCurve.Chart.reciprocal

private theorem chart_inverse {A B X Y : Scheme.{u}} (e : A ≅ B)
    (a : A ⟶ X) (b : B ⟶ Y) (f : X ⟶ Y) (g : Y ⟶ X)
    (h : a ≫ f = e.hom ≫ b) (k : b ≫ g = e.inv ≫ a) :
    a ≫ (f ≫ g) = a ≫ 𝟙 X := by
  rw [← Category.assoc, h, Category.assoc, k, Iso.hom_inv_id_assoc, Category.comp_id]

theorem forward_backward : forward R c hc ≫ backward R c hc = 𝟙 (Order13MixedQuadraticGluedCurve.curveScheme R) := by
  apply (Order13MixedQuadraticGluedCurve.glueData R).openCover.hom_ext
  intro i
  cases i
  · exact chart_inverse (ordinaryIso R c hc) (Order13MixedQuadraticGluedCurve.ordinaryChartMap R) (MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartMap R)
      _ _ (ordinary_forward R c hc) (ordinary_backward R c hc)
  · exact chart_inverse (reciprocalIso R c hc) (Order13MixedQuadraticGluedCurve.reciprocalChartMap R) (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartMap R)
      _ _ (reciprocal_forward R c hc) (reciprocal_backward R c hc)

theorem backward_forward : backward R c hc ≫ forward R c hc = 𝟙 (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme R) := by
  apply (MazurTorsion.XOneThirteenProjectiveCurve.glueData R).openCover.hom_ext
  intro i
  cases i
  · exact chart_inverse (ordinaryIso R c hc).symm (MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartMap R) (Order13MixedQuadraticGluedCurve.ordinaryChartMap R)
      _ _ (ordinary_backward R c hc) (ordinary_forward R c hc)
  · exact chart_inverse (reciprocalIso R c hc).symm (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartMap R) (Order13MixedQuadraticGluedCurve.reciprocalChartMap R)
      _ _ (reciprocal_backward R c hc) (reciprocal_forward R c hc)

def wholeCurveIso : Order13MixedQuadraticGluedCurve.curveScheme R ≅ MazurTorsion.XOneThirteenProjectiveCurve.curveScheme R where
  hom := forward R c hc
  inv := backward R c hc
  hom_inv_id := forward_backward R c hc
  inv_hom_id := backward_forward R c hc


end MazurTransfer.Order13MixedQuadraticWholeCurveComparison
#print axioms MazurTransfer.Order13MixedQuadraticWholeCurveComparison.old_glue
#print axioms MazurTransfer.Order13MixedQuadraticWholeCurveComparison.new_glue

#print axioms MazurTransfer.Order13MixedQuadraticWholeCurveComparison.wholeCurveIso

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual WHOLE completing-square curve isomorphism is
over the coefficient spectrum; its rational specialization is the same
chart comparison already checked. Named downstream consumer: identification
of the whole generic fibre of the dyadic smooth proper family.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticWholeCurveComparisonOverBase
open Polynomial CategoryTheory AlgebraicGeometry
open Order13MixedQuadraticSquareComparisonGenerators Order13MixedQuadraticSquareTransitionSquares
open Order13MixedQuadraticWholeCurveComparison
universe u
variable (R : Type u) [CommRing R] (c : Polynomial R) (hc : 2 * c = 1)

private theorem scalar_spec_comp (A B : Type u) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply DFunLike.ext
  intro r
  exact φ.commutes r

theorem ordinaryIso_toBase : (ordinaryIso R c hc).hom ≫ MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartToBase R = Order13DyadicMixedQuadraticCharts.ordinaryToBase R :=
  scalar_spec_comp R _ _ (ordinaryEquiv R c hc).toAlgHom

theorem reciprocalIso_toBase : (reciprocalIso R c hc).hom ≫ MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartToBase R = Order13DyadicMixedQuadraticCharts.reciprocalToBase R :=
  scalar_spec_comp R _ _ (reciprocalEquiv R c hc).toAlgHom

theorem wholeCurveIso_toBase : (wholeCurveIso R c hc).hom ≫ MazurTorsion.XOneThirteenProjectiveCurve.curveToBase R = Order13MixedQuadraticGluedCurve.curveToBase R := by
  apply (Order13MixedQuadraticGluedCurve.glueData R).openCover.hom_ext
  intro i
  cases i
  · change Order13MixedQuadraticGluedCurve.ordinaryChartMap R ≫ (forward R c hc ≫ MazurTorsion.XOneThirteenProjectiveCurve.curveToBase R) =
      Order13MixedQuadraticGluedCurve.ordinaryChartMap R ≫ Order13MixedQuadraticGluedCurve.curveToBase R
    rw [ordinary_forward_assoc, MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartMap_curveToBase, Order13MixedQuadraticGluedCurve.ordinaryChartMap_curveToBase]
    exact ordinaryIso_toBase R c hc
  · change Order13MixedQuadraticGluedCurve.reciprocalChartMap R ≫ (forward R c hc ≫ MazurTorsion.XOneThirteenProjectiveCurve.curveToBase R) =
      Order13MixedQuadraticGluedCurve.reciprocalChartMap R ≫ Order13MixedQuadraticGluedCurve.curveToBase R
    rw [reciprocal_forward_assoc, MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartMap_curveToBase, Order13MixedQuadraticGluedCurve.reciprocalChartMap_curveToBase]
    exact reciprocalIso_toBase R c hc

theorem wholeCurveIso_inv_toBase : (wholeCurveIso R c hc).inv ≫ Order13MixedQuadraticGluedCurve.curveToBase R = MazurTorsion.XOneThirteenProjectiveCurve.curveToBase R := by
  rw [Iso.inv_comp_eq]
  exact (wholeCurveIso_toBase R c hc).symm

def rationalCurveIso : Order13MixedQuadraticGluedCurve.curveScheme ℚ ≅ MazurTorsion.XOneThirteenProjectiveCurve.curveScheme ℚ :=
  wholeCurveIso ℚ (C ((1 : ℚ) / 2)) Order13MixedQuadraticRationalChartComparison.rational_two_inverse

theorem rationalCurveIso_toBase : rationalCurveIso.hom ≫ MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ = Order13MixedQuadraticGluedCurve.curveToBase ℚ :=
  wholeCurveIso_toBase ℚ _ _

theorem rational_ordinary_iso_agrees :
    ordinaryIso ℚ (C ((1 : ℚ) / 2)) Order13MixedQuadraticRationalChartComparison.rational_two_inverse =
      Order13MixedQuadraticRationalChartComparison.ordinaryRationalSchemeIso := by rfl

theorem rational_reciprocal_iso_agrees :
    reciprocalIso ℚ (C ((1 : ℚ) / 2)) Order13MixedQuadraticRationalChartComparison.rational_two_inverse =
      Order13MixedQuadraticRationalChartComparison.reciprocalRationalSchemeIso := by rfl

end MazurTransfer.Order13MixedQuadraticWholeCurveComparisonOverBase
#print axioms MazurTransfer.Order13MixedQuadraticWholeCurveComparisonOverBase.wholeCurveIso_toBase
#print axioms MazurTransfer.Order13MixedQuadraticWholeCurveComparisonOverBase.rationalCurveIso

end


