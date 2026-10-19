-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualReflectionFunctionFieldOriginalDataAndConstructorCertificates20261018
-- name    : MazurTransfer_Order13ActualReflectionFunctionFieldOriginalDataAndConstructorCertificates20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T21:19:15.252763+00:00
-- url     : https://prove2.me/theorems/32dec7d1-9073-433d-bc21-9b94c08c1c5a
-- title:
--   Original involutive reflection automorphism of the actual scheme function field
-- statement:
--   For every characteristic-zero field and original reflection parameter, the literal reflection coordinates construct the original coordinate-ring map, its injective extension to the actual curve function field, and the original involutive base-field algebra equivalence. The immediate construction certificates retain all original coordinate evaluations, base-field compatibility and square identity. Twenty-three complete original declaration types and six whole constructor values are checked, together with four complete context-provider types and two values, four original constructor proof-helper propositions and the original complete public integral-map injectivity proposition. Named downstream consumer: MazurTransfer.Order13ActualReflectionDiamondRelation.reflectionAlgEquiv_conjugates_diamond. The parameter existence, coordinate identities and transcendence theorem are imported as independently checked public dependencies.
-- source:
--   MazurTheorem Order13ActualReflectionFunctionField, exact original data constructors and immediate construction certificates, with necessary original scalar and denominator proof helpers; original official Anthropic FLT curve/function-field interfaces preserved; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the explicit reflection is an involutive base-field algebra
automorphism of the SAME actual order-13 scheme function field, for each
literal reflection parameter. Named downstream consumer: its actual curve
and Picard lifts, and the arithmetic character of the cyclotomic quotient kernel.
-/
/- Constructor interface: the original reflection coordinate-ring map, fraction-field map and involutive algebra equivalence, with their immediate construction certificates. Named downstream consumer: MazurTransfer.Order13ActualReflectionDiamondRelation.reflectionAlgEquiv_conjugates_diamond. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ReflectionCoordinatesAndParameterOriginalDataSingleUniverseBlockV220261018
import Definitions.Def_MazurTransfer_Order13FieldDiamondFunctionFieldAutomorphismData
import Theorems.Thm_MazurTransfer_order13_reflection_coordinate_certificates
import Theorems.Thm_MazurTransfer_Order13ReflectionParameter_transcendental_reflectionX
noncomputable section
universe u v
namespace MazurTransfer.ReflectionFunctionFieldConstructorProofHelpers20261018
open MazurTransfer.Order13ReflectionSexticSymmetry MazurTransfer.Order13ReflectionParameter Polynomial
variable {F : Type u} [Field F]
theorem scalar_certificate (t : F) :
    (3 * t - 1) * reflectionCubic t + (-3 * t ^ 2 - 8 * t + 12) * reflectionScalar t = 13 := by
  dsimp [reflectionCubic, reflectionScalar]
  ring

theorem scalar_ne_zero [CharZero F] (t : F) (ht : reflectionCubic t = 0) :
    reflectionScalar t ≠ 0 := by
  intro hD
  have h := scalar_certificate t
  rw [ht, hD] at h
  norm_num at h

variable {K : Type u} [Field K]
theorem parameter_scalar_ne_zero [CharZero K] (a : ReflectionParameter K) :
    reflectionScalar a.t ≠ 0 := scalar_ne_zero a.t a.cubic_eq_zero

variable {L : Type v} [Field L] [Algebra K L]
theorem denominator_ne_zero_of_transcendental (t : K) (x : L)
    (hx : Transcendental K x) : reflectionDenominator (algebraMap K L t) x ≠ 0 := by
  intro hz
  by_cases hcoef : algebraMap K L t + 1 = 0
  · simp only [reflectionDenominator, hcoef, zero_mul, zero_add, one_ne_zero] at hz
  · have he : x = -1 / (algebraMap K L t + 1) := by
      apply (eq_div_iff hcoef).mpr
      dsimp [reflectionDenominator] at hz
      linear_combination hz
    apply hx
    rw [he]
    rw [div_eq_mul_inv]
    have ha : IsIntegral K (algebraMap K L t + 1) := isIntegral_algebraMap.add isIntegral_one
    exact ((isIntegral_one (R := K) (B := L)).neg.mul ha.isAlgebraic.inv.isIntegral).isAlgebraic

end MazurTransfer.ReflectionFunctionFieldConstructorProofHelpers20261018
end
noncomputable section
universe u
namespace MazurTransfer.Order13ActualReflectionFunctionField
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
open Order13FieldOrdinaryPolynomialTranscendence Order13FieldDiamondFunctionFieldMap
open Order13FieldDiamondFunctionFieldAutomorphism
open Order13ReflectionSexticSymmetry Order13ReflectionParameter
open MazurTransfer.ReflectionFunctionFieldConstructorProofHelpers20261018
variable (K : Type u) [Field K] [CharZero K]
local instance reflectionFunctionFieldOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance reflectionFunctionFieldOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

abbrev parameterT (a : ReflectionParameter K) : actualCurveFunctionField K :=
  algebraMap K (actualCurveFunctionField K) a.t
abbrev parameterS (a : ReflectionParameter K) : actualCurveFunctionField K :=
  algebraMap K (actualCurveFunctionField K) a.s

theorem parameterT_cubic (a : ReflectionParameter K) : reflectionCubic (parameterT K a) = 0 := by
  have h := congrArg (algebraMap K (actualCurveFunctionField K)) a.cubic_eq_zero
  simpa only [parameterT, reflectionCubic, map_add, map_mul, map_pow,
    map_sub, map_ofNat, map_one, map_zero] using h

theorem parameterS_square (a : ReflectionParameter K) :
    parameterS K a ^ 2 = reflectionScalar (parameterT K a) := by
  have h := congrArg (algebraMap K (actualCurveFunctionField K)) a.square_eq_scalar
  simpa only [parameterS, parameterT, reflectionScalar, map_add, map_pow, map_one] using h

theorem parameterT_scalar_ne_zero (a : ReflectionParameter K) :
    reflectionScalar (parameterT K a) ≠ 0 := by
  have he : algebraMap K (actualCurveFunctionField K) (reflectionScalar a.t) =
      reflectionScalar (parameterT K a) := by
    simp only [reflectionScalar, parameterT, map_add, map_pow, map_one]
  rw [← he]
  exact (_root_.map_ne_zero (algebraMap K (actualCurveFunctionField K))).mpr (parameter_scalar_ne_zero a)

theorem reflection_denominator_ne_zero (a : ReflectionParameter K) :
    reflectionDenominator (parameterT K a) (xImage K) ≠ 0 :=
  denominator_ne_zero_of_transcendental a.t (xImage K) (xImage_transcendental K)

theorem reflection_root (a : ReflectionParameter K) :
    (affineEquation K).eval₂ (aeval (reflectionX (parameterT K a) (xImage K))).toRingHom
      (reflectionY (parameterT K a) (parameterS K a) (xImage K) (yImage K)) = 0 := by
  have h := (MazurTransfer.order13_reflection_coordinate_certificates).1 (parameterT K a) (parameterS K a) (xImage K) (yImage K)
    (parameterT_cubic K a) (parameterS_square K a) (reflection_denominator_ne_zero K a) (yImage_sq K)
  simp only [affineEquation, eval₂_sub, eval₂_X_pow, eval₂_C]
  apply sub_eq_zero.mpr
  change reflectionY (parameterT K a) (parameterS K a) (xImage K) (yImage K) ^ 2 =
    aeval (reflectionX (parameterT K a) (xImage K)) (sexticPolynomial K)
  simpa only [sexticPolynomial, Order13PellChartCertificate.sextic,
    map_add, map_mul, map_pow, map_ofNat, map_one, aeval_X] using h

def ordinaryReflection (a : ReflectionParameter K) : CoordinateRing K →+* actualCurveFunctionField K :=
  AdjoinRoot.lift (aeval (reflectionX (parameterT K a) (xImage K))).toRingHom
    (reflectionY (parameterT K a) (parameterS K a) (xImage K) (yImage K)) (reflection_root K a)

theorem ordinaryReflection_polynomial (a : ReflectionParameter K) (p : Polynomial K) :
    ordinaryReflection K a (AdjoinRoot.of (affineEquation K) p) =
      aeval (reflectionX (parameterT K a) (xImage K)) p := AdjoinRoot.lift_of (reflection_root K a)

theorem ordinaryReflection_x (a : ReflectionParameter K) :
    ordinaryReflection K a (xCoordinate K) = reflectionX (parameterT K a) (xImage K) := by
  rw [xCoordinate, ordinaryReflection_polynomial K a, aeval_X]

theorem ordinaryReflection_y (a : ReflectionParameter K) :
    ordinaryReflection K a (yCoordinate K) =
      reflectionY (parameterT K a) (parameterS K a) (xImage K) (yImage K) :=
  AdjoinRoot.lift_root (reflection_root K a)

theorem ordinaryReflection_injective (a : ReflectionParameter K) :
    Function.Injective (ordinaryReflection K a) := by
  let : Algebra.IsIntegral (Polynomial K) (CoordinateRing K) := ordinary_isIntegral K
  apply MazurTransfer.FieldDiamondMapPublicHelpers20261017.injective_of_integral (Polynomial K) (CoordinateRing K)
    (actualCurveFunctionField K) (ordinaryReflection K a)
  have h : (ordinaryReflection K a).comp (algebraMap (Polynomial K) (CoordinateRing K)) =
      (aeval (reflectionX (parameterT K a) (xImage K))).toRingHom := by
    apply RingHom.ext
    intro p
    exact ordinaryReflection_polynomial K a p
  rw [h]
  exact transcendental_iff_injective.mp
    (transcendental_reflectionX a.t (xImage K) (parameterT_scalar_ne_zero K a) (xImage_transcendental K))

def reflectionFieldMap (a : ReflectionParameter K) : actualCurveFunctionField K →+* actualCurveFunctionField K :=
  IsFractionRing.lift (ordinaryReflection_injective K a)

theorem reflectionFieldMap_coordinate (a : ReflectionParameter K) (b : CoordinateRing K) :
    reflectionFieldMap K a (algebraMap (CoordinateRing K) (actualCurveFunctionField K) b) =
      ordinaryReflection K a b := IsFractionRing.lift_algebraMap (ordinaryReflection_injective K a) b

theorem reflectionFieldMap_x (a : ReflectionParameter K) :
    reflectionFieldMap K a (xImage K) = reflectionX (parameterT K a) (xImage K) :=
  (reflectionFieldMap_coordinate K a (xCoordinate K)).trans (ordinaryReflection_x K a)

theorem reflectionFieldMap_y (a : ReflectionParameter K) :
    reflectionFieldMap K a (yImage K) =
      reflectionY (parameterT K a) (parameterS K a) (xImage K) (yImage K) :=
  (reflectionFieldMap_coordinate K a (yCoordinate K)).trans (ordinaryReflection_y K a)

theorem ordinaryReflection_algebraMap (a : ReflectionParameter K) (r : K) :
    ordinaryReflection K a (algebraMap K (CoordinateRing K) r) =
      algebraMap K (actualCurveFunctionField K) r := by
  change ordinaryReflection K a (AdjoinRoot.of (affineEquation K) (C r)) = _
  rw [ordinaryReflection_polynomial K a, aeval_C]

theorem reflectionFieldMap_algebraMap (a : ReflectionParameter K) (r : K) :
    reflectionFieldMap K a (algebraMap K (actualCurveFunctionField K) r) =
      algebraMap K (actualCurveFunctionField K) r := by
  calc
    _ = reflectionFieldMap K a (algebraMap (CoordinateRing K) (actualCurveFunctionField K)
        (algebraMap K (CoordinateRing K) r)) :=
      congrArg (reflectionFieldMap K a) (ordinaryEmbedding_algebraMap K r).symm
    _ = ordinaryReflection K a (algebraMap K (CoordinateRing K) r) := reflectionFieldMap_coordinate K a _
    _ = _ := ordinaryReflection_algebraMap K a r

theorem map_reflectionX (f : actualCurveFunctionField K →+* actualCurveFunctionField K)
    (t x : actualCurveFunctionField K) : f (reflectionX t x) = reflectionX (f t) (f x) := by
  simp only [reflectionX, reflectionDenominator, map_div₀, map_sub, map_mul, map_add, map_one]

theorem map_reflectionY (f : actualCurveFunctionField K →+* actualCurveFunctionField K)
    (t s x y : actualCurveFunctionField K) :
    f (reflectionY t s x y) = reflectionY (f t) (f s) (f x) (f y) := by
  simp only [reflectionY, reflectionDenominator, map_div₀, map_mul, map_pow, map_add, map_one]

theorem reflectionFieldMap_square (a : ReflectionParameter K) :
    (reflectionFieldMap K a).comp (reflectionFieldMap K a) = RingHom.id _ := by
  apply fieldMap_ext_xy K
  · intro r
    simp only [RingHom.comp_apply, reflectionFieldMap_algebraMap, RingHom.id_apply]
  · simp only [RingHom.comp_apply, reflectionFieldMap_x, map_reflectionX,
      parameterT, reflectionFieldMap_algebraMap, RingHom.id_apply]
    exact (MazurTransfer.order13_reflection_coordinate_certificates).2.1 (parameterT K a) (xImage K)
      (parameterT_scalar_ne_zero K a) (reflection_denominator_ne_zero K a)
  · simp only [RingHom.comp_apply, reflectionFieldMap_y, map_reflectionY,
      parameterT, parameterS, reflectionFieldMap_algebraMap, reflectionFieldMap_x, RingHom.id_apply]
    exact (MazurTransfer.order13_reflection_coordinate_certificates).2.2 (parameterT K a) (parameterS K a) (xImage K) (yImage K)
      (parameterS_square K a) (parameterT_scalar_ne_zero K a) (reflection_denominator_ne_zero K a)

def reflectionRingEquiv (a : ReflectionParameter K) : actualCurveFunctionField K ≃+* actualCurveFunctionField K where
  __ := reflectionFieldMap K a
  invFun := reflectionFieldMap K a
  left_inv x := RingHom.congr_fun (reflectionFieldMap_square K a) x
  right_inv x := RingHom.congr_fun (reflectionFieldMap_square K a) x

def reflectionAlgEquiv (a : ReflectionParameter K) :
    actualCurveFunctionField K ≃ₐ[K] actualCurveFunctionField K :=
  AlgEquiv.ofRingEquiv (f := reflectionRingEquiv K a) (reflectionFieldMap_algebraMap K a)

end MazurTransfer.Order13ActualReflectionFunctionField
#print axioms MazurTransfer.Order13ActualReflectionFunctionField.reflectionFieldMap_square
#print axioms MazurTransfer.Order13ActualReflectionFunctionField.reflectionAlgEquiv


