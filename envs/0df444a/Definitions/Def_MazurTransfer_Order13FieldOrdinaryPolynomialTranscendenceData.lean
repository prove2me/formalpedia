-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldOrdinaryPolynomialTranscendenceData
-- name    : MazurTransfer_Order13FieldOrdinaryPolynomialTranscendenceData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T17:13:23.289636+00:00
-- url     : https://prove2.me/theorems/985f90e9-14b9-49da-b0bc-d60b3aa8020a
-- title:
--   Actual ordinary-coordinate polynomial embeddings over characteristic-zero fields
-- statement:
--   The original polynomial embedding and K-algebra homomorphism into the literal order-thirteen scheme function field, their evaluation formula, abscissa transcendence, denominator nonvanishing and coordinate-algebra integrality, over every characteristic-zero field. Full original types and both data values are preserved, with a separate type/value comparison of the original local scalar algebra provider.
-- source:
--   Original complete MazurTheorem Order13FieldOrdinaryPolynomialTranscendence; public affine-chart scalar compatibility and actual coordinate definitions. Official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual affine coordinate embeddings and polynomial
transcendence over every characteristic-zero base field. Named downstream
consumer: diamond field automorphisms on geometric fibres of the curve.
-/
import Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldScalarCompatibility_coordinateEmbedding_algebraMap
import Definitions.Def_MazurTransfer_Order13ActualOrdinaryFunctionFieldCoordinates

noncomputable section
universe u
namespace MazurTransfer.Order13FieldOrdinaryPolynomialTranscendence
open Polynomial AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

theorem ordinaryEmbedding_algebraMap (r : K) :
    algebraMap (CoordinateRing K) (actualCurveFunctionField K)
      (algebraMap K (CoordinateRing K) r) = algebraMap K (actualCurveFunctionField K) r :=
  AffineOpenChartFunctionFieldScalarCompatibility.coordinateEmbedding_algebraMap
    (.of (CoordinateRing K)) (curveToBase K) (ordinaryChartMap K)
    (ordinaryChartMap_curveToBase K) r

def polynomialEmbedding : Polynomial K →+* actualCurveFunctionField K :=
  (algebraMap (CoordinateRing K) (actualCurveFunctionField K)).comp (AdjoinRoot.of (affineEquation K))

def polynomialAlgHom : Polynomial K →ₐ[K] actualCurveFunctionField K where
  __ := polynomialEmbedding K
  commutes' r := ordinaryEmbedding_algebraMap K r

theorem polynomialAlgHom_eq_aeval : polynomialAlgHom K = aeval (xImage K) := by
  apply Polynomial.algHom_ext
  rw [Polynomial.aeval_X]
  rfl

theorem xImage_transcendental : Transcendental K (xImage K) := by
  apply transcendental_iff_injective.mpr
  rw [← polynomialAlgHom_eq_aeval K]
  exact (IsFractionRing.injective (CoordinateRing K) (actualCurveFunctionField K)).comp
    (Order13SingleSectionFiniteAlgebra.ordinary_polynomial_inclusion_injective K)

theorem xImage_add_one_ne_zero : xImage K + 1 ≠ 0 := by
  intro H
  have Hx : xImage K = -1 := by linear_combination H
  apply xImage_transcendental K
  rw [Hx]
  exact isIntegral_one.neg.isAlgebraic

theorem ordinary_isIntegral : Algebra.IsIntegral (Polynomial K) (CoordinateRing K) := by
  have H : (affineEquation K).Monic := Polynomial.monic_X_pow_sub_C _ (by decide : 2 ≠ 0)
  let : Module.Finite (Polynomial K) (CoordinateRing K) := H.finite_adjoinRoot
  exact Algebra.IsIntegral.of_finite _ _

end MazurTransfer.Order13FieldOrdinaryPolynomialTranscendence
#print axioms MazurTransfer.Order13FieldOrdinaryPolynomialTranscendence.ordinaryEmbedding_algebraMap
#print axioms MazurTransfer.Order13FieldOrdinaryPolynomialTranscendence.xImage_transcendental


