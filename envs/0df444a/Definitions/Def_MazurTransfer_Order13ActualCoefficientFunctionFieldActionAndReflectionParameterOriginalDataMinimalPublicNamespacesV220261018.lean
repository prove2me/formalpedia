-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
-- name    : MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T21:48:42.759407+00:00
-- url     : https://prove2.me/theorems/5ff32770-61ed-4ef0-95e8-678d2a16666b
-- title:
--   Original coefficient action on the actual function field and reflection parameters
-- statement:
--   A coefficient automorphism lifts to the original semilinear automorphism of the same actual curve function field, fixing both displayed curve coordinates and acting as prescribed on the base field. The original reflection parameter is mapped coefficientwise. Twenty-one complete original declaration types and eight whole values are checked, including four own provider types and two values, two context provider types and one value, and the exact original public integral-map injectivity proposition. Named downstream consumer: MazurTransfer.Order13ActualReflectionCoefficientCovariance.coefficientSemilinearAut_reflection. Reflection covariance and the two diamond-commutation identities remain separate mathematical results.
-- source:
--   MazurTheorem Order13ActualFunctionFieldCoefficientAction original coordinate-ring, function-field and semilinear constructors with immediate structural certificates, plus Order13ActualReflectionCoefficientCovariance.mapParameter; original official Anthropic FLT function-field and semilinear interfaces preserved; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: coefficient automorphisms lift canonically to semilinear
automorphisms of the SAME actual order-13 scheme function field, fixing x and y.
Named downstream consumer: semilinear covariance of its actual divisorial
nineteen pairing and comparison with the arithmetic Picard Galois action.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13FieldDiamondFunctionFieldAutomorphismData
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_MazurTransfer_Order13ReflectionCoordinatesAndParameterOriginalDataSingleUniverseBlockV220261018
noncomputable section
universe u
namespace MazurTransfer.Order13ActualFunctionFieldCoefficientAction
open Polynomial AlgebraicCurve
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
open Order13FieldOrdinaryPolynomialTranscendence Order13FieldDiamondFunctionFieldMap
open Order13FieldDiamondFunctionFieldAutomorphism
variable (K : Type u) [Field K] [CharZero K]
local instance coefficientFieldOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance coefficientFieldOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

def coefficientPolynomialMap (σ : K ≃+* K) : Polynomial K →+* actualCurveFunctionField K :=
  (aeval (xImage K)).toRingHom.comp (Polynomial.mapRingHom σ.toRingHom)

theorem coefficientPolynomialMap_sextic (σ : K ≃+* K) :
    coefficientPolynomialMap K σ (sexticPolynomial K) =
      Order13PellChartCertificate.sextic (xImage K) := by
  change aeval (xImage K) ((sexticPolynomial K).map σ.toRingHom) = _
  simp only [sexticPolynomial, Order13PellChartCertificate.sextic,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, Polynomial.map_one, map_add, map_mul, map_pow, map_ofNat,
    map_one, aeval_X]

theorem coefficient_root (σ : K ≃+* K) :
    (affineEquation K).eval₂ (coefficientPolynomialMap K σ) (yImage K) = 0 := by
  simp only [affineEquation, eval₂_sub, eval₂_X_pow, eval₂_C]
  rw [coefficientPolynomialMap_sextic K σ, yImage_sq K, sub_self]

def ordinaryCoefficientMap (σ : K ≃+* K) : CoordinateRing K →+* actualCurveFunctionField K :=
  AdjoinRoot.lift (coefficientPolynomialMap K σ) (yImage K) (coefficient_root K σ)

theorem ordinaryCoefficientMap_polynomial (σ : K ≃+* K) (p : Polynomial K) :
    ordinaryCoefficientMap K σ (AdjoinRoot.of (affineEquation K) p) =
      coefficientPolynomialMap K σ p := AdjoinRoot.lift_of (coefficient_root K σ)

theorem ordinaryCoefficientMap_injective (σ : K ≃+* K) :
    Function.Injective (ordinaryCoefficientMap K σ) := by
  let : Algebra.IsIntegral (Polynomial K) (CoordinateRing K) := ordinary_isIntegral K
  apply MazurTransfer.FieldDiamondMapPublicHelpers20261017.injective_of_integral (Polynomial K) (CoordinateRing K)
    (actualCurveFunctionField K) (ordinaryCoefficientMap K σ)
  have h : (ordinaryCoefficientMap K σ).comp (algebraMap (Polynomial K) (CoordinateRing K)) =
      coefficientPolynomialMap K σ := by
    apply RingHom.ext
    intro p
    exact ordinaryCoefficientMap_polynomial K σ p
  rw [h]
  exact (transcendental_iff_injective.mp (xImage_transcendental K)).comp
    (Polynomial.map_injective σ.toRingHom σ.injective)

def coefficientFieldMap (σ : K ≃+* K) : actualCurveFunctionField K →+* actualCurveFunctionField K :=
  IsFractionRing.lift (ordinaryCoefficientMap_injective K σ)

theorem coefficientFieldMap_coordinate (σ : K ≃+* K) (b : CoordinateRing K) :
    coefficientFieldMap K σ (algebraMap (CoordinateRing K) (actualCurveFunctionField K) b) =
      ordinaryCoefficientMap K σ b := IsFractionRing.lift_algebraMap _ b

theorem coefficientFieldMap_x (σ : K ≃+* K) : coefficientFieldMap K σ (xImage K) = xImage K := by
  change coefficientFieldMap K σ
    (algebraMap (CoordinateRing K) (actualCurveFunctionField K) (xCoordinate K)) = xImage K
  rw [coefficientFieldMap_coordinate K σ, xCoordinate, ordinaryCoefficientMap_polynomial K σ]
  change aeval (xImage K) ((X : Polynomial K).map σ.toRingHom) = xImage K
  rw [Polynomial.map_X, aeval_X]

theorem coefficientFieldMap_y (σ : K ≃+* K) : coefficientFieldMap K σ (yImage K) = yImage K :=
  (coefficientFieldMap_coordinate K σ (yCoordinate K)).trans
    (AdjoinRoot.lift_root (coefficient_root K σ))

theorem coefficientFieldMap_algebraMap (σ : K ≃+* K) (r : K) :
    coefficientFieldMap K σ (algebraMap K (actualCurveFunctionField K) r) =
      algebraMap K (actualCurveFunctionField K) (σ r) := by
  rw [← ordinaryEmbedding_algebraMap K r, coefficientFieldMap_coordinate K σ]
  change ordinaryCoefficientMap K σ (AdjoinRoot.of (affineEquation K) (C r)) = _
  rw [ordinaryCoefficientMap_polynomial K σ]
  change aeval (xImage K) ((C r).map σ.toRingHom) = _
  rw [Polynomial.map_C, aeval_C]
  rfl

theorem coefficientFieldMap_one : coefficientFieldMap K (1 : K ≃+* K) = RingHom.id _ := by
  apply fieldMap_ext_xy K
  · intro r
    exact coefficientFieldMap_algebraMap K 1 r
  · exact coefficientFieldMap_x K 1
  · exact coefficientFieldMap_y K 1

theorem coefficientFieldMap_mul (σ τ : K ≃+* K) :
    coefficientFieldMap K (σ * τ) = (coefficientFieldMap K σ).comp (coefficientFieldMap K τ) := by
  apply fieldMap_ext_xy K
  · intro r
    simp only [RingHom.comp_apply, coefficientFieldMap_algebraMap]
    rfl
  · simp only [RingHom.comp_apply, coefficientFieldMap_x]
  · simp only [RingHom.comp_apply, coefficientFieldMap_y]

def coefficientFieldEquiv (σ : K ≃+* K) : actualCurveFunctionField K ≃+* actualCurveFunctionField K where
  __ := coefficientFieldMap K σ
  invFun := coefficientFieldMap K σ⁻¹
  left_inv x := by
    have h := RingHom.congr_fun (coefficientFieldMap_mul K σ⁻¹ σ) x
    rw [inv_mul_cancel, coefficientFieldMap_one K] at h
    exact h.symm
  right_inv x := by
    have h := RingHom.congr_fun (coefficientFieldMap_mul K σ σ⁻¹) x
    rw [mul_inv_cancel, coefficientFieldMap_one K] at h
    exact h.symm

def coefficientSemilinearAut (σ : K ≃+* K) : SemilinearAut K (actualCurveFunctionField K) :=
  ⟨(coefficientFieldEquiv K σ, σ), coefficientFieldMap_algebraMap K σ⟩

def coefficientSemilinearHom : (K ≃+* K) →* SemilinearAut K (actualCurveFunctionField K) where
  toFun := coefficientSemilinearAut K
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · apply RingEquiv.ext
      intro x
      exact RingHom.congr_fun (coefficientFieldMap_one K) x
    · rfl
  map_mul' σ τ := by
    apply Subtype.ext
    apply Prod.ext
    · apply RingEquiv.ext
      intro x
      exact RingHom.congr_fun (coefficientFieldMap_mul K σ τ) x
    · rfl

theorem coefficientSemilinearAut_baseAut (σ : K ≃+* K) :
    SemilinearAut.baseAut (coefficientSemilinearAut K σ) = σ := rfl

def galoisSemilinearHom : (K ≃ₐ[ℚ] K) →* SemilinearAut K (actualCurveFunctionField K) :=
  (coefficientSemilinearHom K).comp
    { toFun := fun σ => σ.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem galoisSemilinearHom_baseAut (σ : K ≃ₐ[ℚ] K) :
    SemilinearAut.baseAut (galoisSemilinearHom K σ) = σ.toRingEquiv := rfl

theorem coefficientFieldMap_unique (σ : K ≃+* K)
    (f : actualCurveFunctionField K →+* actualCurveFunctionField K)
    (hc : ∀ r : K, f (algebraMap K (actualCurveFunctionField K) r) =
      algebraMap K (actualCurveFunctionField K) (σ r))
    (hx : f (xImage K) = xImage K) (hy : f (yImage K) = yImage K) :
    f = coefficientFieldMap K σ := by
  apply fieldMap_ext_xy K
  · intro r
    exact (hc r).trans (coefficientFieldMap_algebraMap K σ r).symm
  · exact hx.trans (coefficientFieldMap_x K σ).symm
  · exact hy.trans (coefficientFieldMap_y K σ).symm

end MazurTransfer.Order13ActualFunctionFieldCoefficientAction

namespace MazurTransfer.Order13ActualReflectionCoefficientCovariance
open AlgebraicCurve
open Order13ReflectionSexticSymmetry Order13ReflectionParameter
open Order13ActualFunctionFieldCoefficientAction
open Order13FieldDiamondFunctionFieldAutomorphism
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart
variable (K : Type u) [Field K] [CharZero K]
local instance reflectionCoefficientOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance reflectionCoefficientOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

def mapParameter (σ : K ≃+* K) (a : ReflectionParameter K) : ReflectionParameter K where
  t := σ a.t
  s := σ a.s
  cubic_eq_zero := by
    have h := congrArg σ a.cubic_eq_zero
    simpa only [reflectionCubic, map_add, map_mul, map_pow, map_sub,
      map_ofNat, map_one, map_zero] using h
  square_eq_scalar := by
    have h := congrArg σ a.square_eq_scalar
    simpa only [reflectionScalar, map_add, map_pow, map_one] using h

end MazurTransfer.Order13ActualReflectionCoefficientCovariance

#print axioms MazurTransfer.Order13ActualFunctionFieldCoefficientAction.galoisSemilinearHom
#print axioms MazurTransfer.Order13ActualReflectionCoefficientCovariance.mapParameter


