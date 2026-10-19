-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalRationalChartComparisonAndAffineBaseChangeData20261019
-- name    : MazurTransfer_Order13MixedQuadraticOriginalRationalChartComparisonAndAffineBaseChangeData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T04:48:08.273602+00:00
-- url     : https://prove2.me/theorems/15aaf96e-ee41-4083-93a4-5fb6c5c0472e
-- title:
--   Original mixed quadratic rational chart and affine base-change isomorphisms
-- statement:
--   The original completing-square identifications with the SAME original rational order-thirteen coordinate rings, both whole affine base-change isomorphisms, and both actual dyadic rational affine-fibre isomorphisms. Forty-five original types and twelve whole nonproof values are checked, including the exact inspected prime-provider type. Named downstream consumer: whole-curve base change and the compatible rational Picard comparison.
-- source:
--   MazurTheorem original mixed quadratic scalar extension, completing square, rational chart comparison and affine base change; Vas and contributors; Apache-2.0.

import Definitions.Def_MazurTransfer_MixedQuadraticOriginalScalarExtensionAndCompletingSquareData20261019
import Definitions.Def_MazurTransfer_Order13DyadicMixedOriginalAffineChartData20261019
import Definitions.Def_MazurTransfer_Order13IntegralBaseAndFieldMaps
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual algebra equivalences and affine scheme isomorphisms
between the literal rational mixed quadratic charts and the SAME existing
order-thirteen curve coordinate rings. Named downstream consumer: gluing
and generic-fibre comparison of the dyadic integral chart schemes.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticRationalChartComparison
open Polynomial CategoryTheory AlgebraicGeometry
open MixedQuadraticCompletingSquare Order13MixedQuadraticJacobianCertificates
open Order13DyadicMixedQuadraticCharts
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (R : Type u) [CommRing R]

theorem ordinary_discriminant_identity : (ordinaryH R) ^ 2 + 4 * ordinaryF R = sexticPolynomial R := by
  dsimp [ordinaryH, ordinaryF, sexticPolynomial]
  ring

theorem reciprocal_discriminant_identity : (reciprocalH R) ^ 2 + 4 * reciprocalF R = reciprocalPolynomial R := by
  dsimp [reciprocalH, reciprocalF, reciprocalPolynomial]
  ring

def ordinaryChartEquiv (c : Polynomial R) (hc : 2 * c = 1) :
    ordinaryCoordinateRing R ≃ₐ[Polynomial R] CoordinateRing R := by
  exact (completingSquareEquiv (Polynomial R) (ordinaryH R) (ordinaryF R) c hc).trans
    (AdjoinRoot.algEquivOfEq (Polynomial R) _ (affineEquation R) (by
      unfold squarePolynomial
      rw [ordinary_discriminant_identity]
      rfl))

def reciprocalChartEquiv (c : Polynomial R) (hc : 2 * c = 1) :
    reciprocalCoordinateRing R ≃ₐ[Polynomial R] ReciprocalRing R := by
  exact (completingSquareEquiv (Polynomial R) (reciprocalH R) (reciprocalF R) c hc).trans
    (AdjoinRoot.algEquivOfEq (Polynomial R) _ (reciprocalEquation R) (by
      unfold squarePolynomial
      rw [reciprocal_discriminant_identity]
      rfl))

theorem rational_two_inverse : (2 : Polynomial ℚ) * C ((1 : ℚ) / 2) = 1 := by
  simpa only [map_mul, map_ofNat, map_one] using
    congrArg (C : ℚ →+* Polynomial ℚ) (show (2 : ℚ) * (1 / 2) = 1 by norm_num)

def ordinaryRationalEquiv : ordinaryCoordinateRing ℚ ≃ₐ[ℚ] CoordinateRing ℚ :=
  (ordinaryChartEquiv ℚ (C ((1 : ℚ) / 2)) rational_two_inverse).restrictScalars ℚ

def reciprocalRationalEquiv : reciprocalCoordinateRing ℚ ≃ₐ[ℚ] ReciprocalRing ℚ :=
  (reciprocalChartEquiv ℚ (C ((1 : ℚ) / 2)) rational_two_inverse).restrictScalars ℚ

def ordinaryRationalSchemeIso : ordinaryScheme ℚ ≅ MazurTorsion.XOneThirteenAffineCurve.scheme ℚ :=
  (Scheme.Spec.mapIso ordinaryRationalEquiv.toRingEquiv.toCommRingCatIso.op).symm

def reciprocalRationalSchemeIso : Order13DyadicMixedQuadraticCharts.reciprocalScheme ℚ ≅ MazurTorsion.XOneThirteenProjectiveCurve.reciprocalScheme ℚ :=
  (Scheme.Spec.mapIso reciprocalRationalEquiv.toRingEquiv.toCommRingCatIso.op).symm

end MazurTransfer.Order13MixedQuadraticRationalChartComparison
#print axioms MazurTransfer.Order13MixedQuadraticRationalChartComparison.ordinaryRationalSchemeIso
#print axioms MazurTransfer.Order13MixedQuadraticRationalChartComparison.reciprocalRationalSchemeIso

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: genuine base-change isomorphisms for both mixed quadratic
affine charts, and their actual dyadic rational fibres identified with the
SAME existing order-thirteen affine curve charts. Named downstream consumer:
gluing the dyadic integral curve and proving its proper generic comparison.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticAffineBaseChange
open Polynomial Algebra TensorProduct CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MixedQuadraticCoordinateJacobian Order13MixedQuadraticJacobianCertificates
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticRationalChartComparison
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem ordinaryH_map : (ordinaryH R).map (algebraMap R S) = ordinaryH S := by simp [ordinaryH]
theorem ordinaryF_map : (ordinaryF R).map (algebraMap R S) = ordinaryF S := by simp [ordinaryF]
theorem reciprocalH_map : (reciprocalH R).map (algebraMap R S) = reciprocalH S := by simp [reciprocalH]
theorem reciprocalF_map : (reciprocalF R).map (algebraMap R S) = reciprocalF S := by simp [reciprocalF]

def ordinaryAlgebraEquiv : S ⊗[R] ordinaryCoordinateRing R ≃ₐ[S] ordinaryCoordinateRing S :=
  (MixedQuadraticCoordinateBaseChange.coordinateRingEquiv R S (ordinaryH R) (ordinaryF R)).trans
    (AdjoinRoot.algEquivOfEq S _ (equation S (ordinaryH S) (ordinaryF S)) (by
      rw [ordinaryH_map R S, ordinaryF_map R S]))

def reciprocalAlgebraEquiv : S ⊗[R] reciprocalCoordinateRing R ≃ₐ[S] reciprocalCoordinateRing S :=
  (MixedQuadraticCoordinateBaseChange.coordinateRingEquiv R S (reciprocalH R) (reciprocalF R)).trans
    (AdjoinRoot.algEquivOfEq S _ (equation S (reciprocalH S) (reciprocalF S)) (by
      rw [reciprocalH_map R S, reciprocalF_map R S]))

def ordinaryChartIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (ordinaryToBase R) ≅ ordinaryScheme S := by
  unfold ordinaryToBase ordinaryScheme
  exact (pullbackSpecIso R S (ordinaryCoordinateRing R)).trans
    (Scheme.Spec.mapIso (ordinaryAlgebraEquiv R S).symm.toRingEquiv.toCommRingCatIso.op)

def reciprocalChartIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (reciprocalToBase R) ≅ reciprocalScheme S := by
  unfold reciprocalToBase reciprocalScheme
  exact (pullbackSpecIso R S (reciprocalCoordinateRing R)).trans
    (Scheme.Spec.mapIso (reciprocalAlgebraEquiv R S).symm.toRingEquiv.toCommRingCatIso.op)

theorem ordinaryChartIso_inv_fst : (ordinaryChartIso R S).inv ≫ pullback.fst _ _ = ordinaryToBase S := by
  change (Spec.map (CommRingCat.ofHom (ordinaryAlgebraEquiv R S).toRingHom) ≫
    (pullbackSpecIso R S (ordinaryCoordinateRing R)).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst']
  unfold ordinaryToBase
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext s
  exact (ordinaryAlgebraEquiv R S).commutes s

theorem reciprocalChartIso_inv_fst : (reciprocalChartIso R S).inv ≫ pullback.fst _ _ = reciprocalToBase S := by
  change (Spec.map (CommRingCat.ofHom (reciprocalAlgebraEquiv R S).toRingHom) ≫
    (pullbackSpecIso R S (reciprocalCoordinateRing R)).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst']
  unfold reciprocalToBase
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext s
  exact (reciprocalAlgebraEquiv R S).commutes s

def ordinaryDyadicRationalFibreIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap BaseRing ℚ))) (ordinaryToBase BaseRing) ≅
      MazurTorsion.XOneThirteenAffineCurve.scheme ℚ :=
  (ordinaryChartIso BaseRing ℚ).trans ordinaryRationalSchemeIso

def reciprocalDyadicRationalFibreIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap BaseRing ℚ))) (reciprocalToBase BaseRing) ≅
      MazurTorsion.XOneThirteenProjectiveCurve.reciprocalScheme ℚ :=
  (reciprocalChartIso BaseRing ℚ).trans reciprocalRationalSchemeIso

theorem ordinaryRationalSchemeIso_inv_toBase :
    ordinaryRationalSchemeIso.inv ≫ ordinaryToBase ℚ =
      MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartToBase ℚ := by
  change Spec.map (CommRingCat.ofHom ordinaryRationalEquiv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (ordinaryCoordinateRing ℚ))) =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (MazurTorsion.XOneThirteenAffineCurve.CoordinateRing ℚ)))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext s
  exact ordinaryRationalEquiv.commutes s

theorem reciprocalRationalSchemeIso_inv_toBase :
    reciprocalRationalSchemeIso.inv ≫ reciprocalToBase ℚ =
      MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartToBase ℚ := by
  change Spec.map (CommRingCat.ofHom reciprocalRationalEquiv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (reciprocalCoordinateRing ℚ))) =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalRing ℚ)))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext s
  exact reciprocalRationalEquiv.commutes s

theorem actual_ordinary_dyadic_rational_fibre :
    ordinaryDyadicRationalFibreIso.inv ≫ pullback.fst _ _ =
      MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartToBase ℚ := by
  change (ordinaryRationalSchemeIso.inv ≫ (ordinaryChartIso BaseRing ℚ).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, ordinaryChartIso_inv_fst, ordinaryRationalSchemeIso_inv_toBase]

theorem actual_reciprocal_dyadic_rational_fibre :
    reciprocalDyadicRationalFibreIso.inv ≫ pullback.fst _ _ =
      MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartToBase ℚ := by
  change (reciprocalRationalSchemeIso.inv ≫ (reciprocalChartIso BaseRing ℚ).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, reciprocalChartIso_inv_fst, reciprocalRationalSchemeIso_inv_toBase]

end MazurTransfer.Order13MixedQuadraticAffineBaseChange
#print axioms MazurTransfer.Order13MixedQuadraticAffineBaseChange.actual_ordinary_dyadic_rational_fibre
#print axioms MazurTransfer.Order13MixedQuadraticAffineBaseChange.actual_reciprocal_dyadic_rational_fibre

end


