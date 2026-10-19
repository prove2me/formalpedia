-- Prove2me | Definitions.Def_MazurTransfer_Order13OrdinaryLocalOriginalDataAndCertificates20261018
-- name    : MazurTransfer_Order13OrdinaryLocalOriginalDataAndCertificates20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T19:04:26.291241+00:00
-- url     : https://prove2.me/theorems/e955622f-3ef4-4fe0-a8eb-c02c43abece7
-- title:
--   Original ordinary evaluation and discrete valuation ring interface
-- statement:
--   Retain the original ordinary evaluation quotient, local coordinate and parameter constructors, and their exact evaluation-kernel, maximal-ideal and discrete valuation ring certificates. All twenty-nine complete original declaration types and all eleven nonproof values are compared. Named downstream consumer is the cubic function cusp-order calculation; all original fields and characteristic hypotheses remain.
-- source:
--   Original retained MazurTheorem cubic and local-ring modules, Apache-2.0, Vas and contributors. Complete original declaration types and whole nonproof constructor values are compared. This packages existing checked constructors and their proved certificates; it adds no arithmetic assumption or new theorem acceptance credit.

import Mathlib
import Definitions.Def_MazurTransfer_Order13SixMarkedIntegralSections
import Definitions.Def_MazurTransfer_Order13CubicNormChartOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_Order13FieldOrdinaryPolynomialTranscendenceData
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the retained original ordinary evaluation quotient, local coordinate and parameter constructors, with their exact kernel, maximal-ideal and discrete valuation ring certificates. Named downstream consumer: Order13CubicCuspLocalOrders for the cubic principal divisor and infinity-class norm eigenvalue. All original fields and characteristic hypotheses are retained. These are packaged original interfaces and certificates; no additional arithmetic hypothesis is introduced.
-/
universe u
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact evaluation ideal at every literal ordinary
chart point over a commutative base ring. Named downstream consumer:
ordinary cusp local parameters and the cubic principal divisor.
-/

noncomputable section
namespace MazurTransfer.Order13OrdinaryEvaluationKernel
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open Order13IntegralSections
variable (R : Type u) [CommRing R] (t a : R) (ha : a ^ 2 = (sexticPolynomial R).eval t)

def evaluation : CoordinateRing R →+* R := ordinaryEvaluation R t a ha
def evaluationAlgHom : CoordinateRing R →ₐ[R] R where
  __ := evaluation R t a ha
  commutes' r := by
    exact RingHom.congr_fun (ordinaryEvaluation_comp_algebraMap R t a ha) r

def sectionIdeal : Ideal (CoordinateRing R) :=
  Ideal.span {xCoordinate R - algebraMap R (CoordinateRing R) t, yCoordinate R - algebraMap R (CoordinateRing R) a}

def quotientMap : CoordinateRing R →ₐ[R] CoordinateRing R ⧸ sectionIdeal R t a :=
  Ideal.Quotient.mkₐ R (sectionIdeal R t a)

theorem quotientMap_x : quotientMap R t a (xCoordinate R) = algebraMap R (CoordinateRing R ⧸ sectionIdeal R t a) t := by
  have h : quotientMap R t a (xCoordinate R - algebraMap R (CoordinateRing R) t) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))
  rw [map_sub, (quotientMap R t a).commutes] at h
  exact sub_eq_zero.mp h

theorem quotientMap_y : quotientMap R t a (yCoordinate R) =
    algebraMap R (CoordinateRing R ⧸ sectionIdeal R t a) a := by
  have h : quotientMap R t a (yCoordinate R - algebraMap R (CoordinateRing R) a) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))
  rw [map_sub, (quotientMap R t a).commutes] at h
  exact sub_eq_zero.mp h

theorem quotientMap_factorization : quotientMap R t a =
    (Algebra.ofId R (CoordinateRing R ⧸ sectionIdeal R t a)).comp
      (evaluationAlgHom R t a ha) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change quotientMap R t a (xCoordinate R) =
      algebraMap R (CoordinateRing R ⧸ sectionIdeal R t a)
        (ordinaryEvaluation R t a ha (xCoordinate R))
    rw [quotientMap_x, ordinaryEvaluation_x]
  · change quotientMap R t a (yCoordinate R) =
      algebraMap R (CoordinateRing R ⧸ sectionIdeal R t a)
        (ordinaryEvaluation R t a ha (yCoordinate R))
    rw [quotientMap_y, ordinaryEvaluation_y]

theorem sectionIdeal_le_kernel : sectionIdeal R t a ≤ RingHom.ker (evaluation R t a ha) := by
  apply Ideal.span_le.mpr
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl
  · change evaluation R t a ha (xCoordinate R - algebraMap R (CoordinateRing R) t) = 0
    rw [map_sub]
    change ordinaryEvaluation R t a ha (xCoordinate R) - ordinaryEvaluation R t a ha (algebraMap R (CoordinateRing R) t) = 0
    rw [ordinaryEvaluation_x]
    have h := RingHom.congr_fun (ordinaryEvaluation_comp_algebraMap R t a ha) t
    change ordinaryEvaluation R t a ha (algebraMap R (CoordinateRing R) t) = t at h
    rw [h, sub_self]
  · change evaluation R t a ha (yCoordinate R - algebraMap R (CoordinateRing R) a) = 0
    rw [map_sub]
    change ordinaryEvaluation R t a ha (yCoordinate R) -
      ordinaryEvaluation R t a ha (algebraMap R (CoordinateRing R) a) = 0
    have h := RingHom.congr_fun (ordinaryEvaluation_comp_algebraMap R t a ha) a
    change ordinaryEvaluation R t a ha (algebraMap R (CoordinateRing R) a) = a at h
    rw [ordinaryEvaluation_y, h]
    exact sub_self a

theorem evaluation_kernel : RingHom.ker (evaluation R t a ha) = sectionIdeal R t a := by
  apply le_antisymm
  · intro b hb
    change evaluation R t a ha b = 0 at hb
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change quotientMap R t a b = 0
    have h := DFunLike.congr_fun (quotientMap_factorization R t a ha) b
    change quotientMap R t a b =
      algebraMap R (CoordinateRing R ⧸ sectionIdeal R t a) (evaluation R t a ha b) at h
    rw [hb, map_zero] at h
    exact h
  · exact sectionIdeal_le_kernel R t a ha

theorem evaluation_surjective : Function.Surjective (evaluation R t a ha) := by
  intro r
  refine ⟨algebraMap R (CoordinateRing R) r, ?_⟩
  exact RingHom.congr_fun (ordinaryEvaluation_comp_algebraMap R t a ha) r

end MazurTransfer.Order13OrdinaryEvaluationKernel
#print axioms MazurTransfer.Order13OrdinaryEvaluationKernel.evaluation_kernel
#print axioms MazurTransfer.Order13OrdinaryEvaluationKernel.evaluation_surjective

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: x-t generates the maximal ideal of the ordinary-chart
localization at (t,a) whenever 2a is nonzero. Named downstream consumer:
cusp discrete valuation rings and the cubic principal divisor.
-/

noncomputable section
namespace MazurTransfer.Order13OrdinaryLocalParameter
open MazurTorsion.XOneThirteenAffineCurve
open Order13OrdinaryEvaluationKernel Polynomial
variable (K : Type u) [Field K] (t a : K)
    (ha : a ^ 2 = (sexticPolynomial K).eval t)

def pointIdeal : Ideal (CoordinateRing K) := RingHom.ker (evaluation K t a ha)
instance pointIdeal_isPrime : (pointIdeal K t a ha).IsPrime := RingHom.ker_isPrime _
instance pointIdeal_isMaximal : (pointIdeal K t a ha).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (evaluation_surjective K t a ha)
abbrev LocalRing := Localization.AtPrime (pointIdeal K t a ha)
def x : LocalRing K t a ha := algebraMap (CoordinateRing K) (LocalRing K t a ha) (xCoordinate K)
def y : LocalRing K t a ha := algebraMap (CoordinateRing K) (LocalRing K t a ha) (yCoordinate K)
def constant (r : K) : LocalRing K t a ha :=
  algebraMap (CoordinateRing K) (LocalRing K t a ha) (algebraMap K (CoordinateRing K) r)
def parameter : LocalRing K t a ha := x K t a ha - constant K t a ha t

def sexticSecant {R : Type u} [CommRing R] (x t : R) : R :=
  (x ^ 5 + x ^ 4 * t + x ^ 3 * t ^ 2 + x ^ 2 * t ^ 3 + x * t ^ 4 + t ^ 5) +
  2 * (x ^ 4 + x ^ 3 * t + x ^ 2 * t ^ 2 + x * t ^ 3 + t ^ 4) +
  (x ^ 3 + x ^ 2 * t + x * t ^ 2 + t ^ 3) +
  2 * (x ^ 2 + x * t + t ^ 2) + 6 * (x + t) + 4

theorem sextic_difference {R : Type u} [CommRing R] (x t : R) :
    Order13PellChartCertificate.sextic x - Order13PellChartCertificate.sextic t =
      (x - t) * sexticSecant x t := by
  dsimp [Order13PellChartCertificate.sextic, sexticSecant]
  ring

theorem y_add_constant_isUnit (hc : 2 * a ≠ 0) :
    IsUnit (y K t a ha + constant K t a ha a) := by
  dsimp [y, constant]
  rw [← map_add]
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (LocalRing K t a ha) (pointIdeal K t a ha) _).mpr
  change evaluation K t a ha (yCoordinate K + algebraMap K (CoordinateRing K) a) ≠ 0
  have hconst := RingHom.congr_fun (Order13IntegralSections.ordinaryEvaluation_comp_algebraMap K t a ha) a
  change evaluation K t a ha (algebraMap K (CoordinateRing K) a) = a at hconst
  have hy : evaluation K t a ha (yCoordinate K) = a := Order13IntegralSections.ordinaryEvaluation_y K t a ha
  rw [map_add, hy, hconst, ← two_mul]
  exact hc

theorem difference_product :
    (y K t a ha - constant K t a ha a) * (y K t a ha + constant K t a ha a) =
      parameter K t a ha * sexticSecant (x K t a ha) (constant K t a ha t) := by
  have hy := congrArg (algebraMap (CoordinateRing K) (LocalRing K t a ha)) (yCoordinate_sq K)
  have hc := congrArg ((algebraMap (CoordinateRing K) (LocalRing K t a ha)).comp
    (algebraMap K (CoordinateRing K))) ha
  simp only [sexticPolynomial, map_add, map_mul, map_pow, map_ofNat, map_one, aeval_X] at hy
  simp only [RingHom.comp_apply, sexticPolynomial, map_add, map_mul, map_pow, map_ofNat, map_one,
    eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one] at hc
  change y K t a ha ^ 2 = Order13PellChartCertificate.sextic (x K t a ha) at hy
  change constant K t a ha a ^ 2 = Order13PellChartCertificate.sextic (constant K t a ha t) at hc
  calc
    _ = y K t a ha ^ 2 - constant K t a ha a ^ 2 := by ring
    _ = Order13PellChartCertificate.sextic (x K t a ha) - Order13PellChartCertificate.sextic (constant K t a ha t) := by rw [hy, hc]
    _ = _ := sextic_difference _ _

theorem difference_mem_span_parameter (hc : 2 * a ≠ 0) :
    y K t a ha - constant K t a ha a ∈ Ideal.span {parameter K t a ha} := by
  apply (Ideal.mul_unit_mem_iff_mem _ (y_add_constant_isUnit K t a ha hc)).mp
  rw [difference_product]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem maximalIdeal_eq_span_parameter (hc : 2 * a ≠ 0) :
    IsLocalRing.maximalIdeal (LocalRing K t a ha) = Ideal.span {parameter K t a ha} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    change RingHom.ker (evaluation K t a ha) ≤ _
    rw [evaluation_kernel]
    apply Ideal.span_le.mpr
    intro b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · change algebraMap (CoordinateRing K) (LocalRing K t a ha)
        (xCoordinate K - algebraMap K (CoordinateRing K) t) ∈ Ideal.span {parameter K t a ha}
      rw [map_sub]
      exact Ideal.subset_span (by simp [parameter, x, constant])
    · change algebraMap (CoordinateRing K) (LocalRing K t a ha)
        (yCoordinate K - algebraMap K (CoordinateRing K) a) ∈ Ideal.span {parameter K t a ha}
      rw [map_sub]
      exact difference_mem_span_parameter K t a ha hc
  · apply Ideal.span_le.mpr
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst b
    change algebraMap (CoordinateRing K) (LocalRing K t a ha) (xCoordinate K) -
      algebraMap (CoordinateRing K) (LocalRing K t a ha) (algebraMap K (CoordinateRing K) t) ∈
      Ideal.map (algebraMap (CoordinateRing K) (LocalRing K t a ha)) (pointIdeal K t a ha)
    rw [← map_sub]
    apply Ideal.mem_map_of_mem
    change evaluation K t a ha (xCoordinate K - algebraMap K (CoordinateRing K) t) = 0
    rw [map_sub]
    have hx := Order13IntegralSections.ordinaryEvaluation_x K t a ha
    change evaluation K t a ha (xCoordinate K) = t at hx
    have ht := RingHom.congr_fun (Order13IntegralSections.ordinaryEvaluation_comp_algebraMap K t a ha) t
    change evaluation K t a ha (algebraMap K (CoordinateRing K) t) = t at ht
    rw [hx, ht, sub_self]

end MazurTransfer.Order13OrdinaryLocalParameter
#print axioms MazurTransfer.Order13OrdinaryLocalParameter.maximalIdeal_eq_span_parameter

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the ordinary evaluation localizations with 2a nonzero
are discrete valuation rings, with x-t irreducible. Named downstream
consumer: exact finite cusp orders of the cubic functions.
-/

noncomputable section
namespace MazurTransfer.Order13OrdinaryDiscreteValuationRing
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open Order13OrdinaryLocalParameter
variable (K : Type u) [Field K] [CharZero K] (t a : K)
    (ha : a ^ 2 = (sexticPolynomial K).eval t)

theorem coordinate_difference_ne_zero : xCoordinate K - algebraMap K (CoordinateRing K) t ≠ 0 := by
  have h := Order13SingleSectionFiniteAlgebra.ordinary_polynomial_inclusion_injective K
  have hn := (map_ne_zero_iff (AdjoinRoot.of (affineEquation K)) h).mpr (X_sub_C_ne_zero t)
  simpa only [map_sub, xCoordinate, AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_eq] using hn

theorem parameter_ne_zero : parameter K t a ha ≠ 0 := by
  change algebraMap (CoordinateRing K) (LocalRing K t a ha) (xCoordinate K) -
    algebraMap (CoordinateRing K) (LocalRing K t a ha) (algebraMap K (CoordinateRing K) t) ≠ 0
  rw [← map_sub]
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (CoordinateRing K) (LocalRing K t a ha))).mpr
    (coordinate_difference_ne_zero K t)

theorem localRing_not_isField (hc : 2 * a ≠ 0) : ¬ IsField (LocalRing K t a ha) := by
  intro h
  have hu : parameter K t a ha ∈ IsLocalRing.maximalIdeal (LocalRing K t a ha) := by
    rw [maximalIdeal_eq_span_parameter K t a ha hc]
    exact Ideal.subset_span (by simp)
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp h] at hu
  exact parameter_ne_zero K t a ha hu

instance localRing_isDiscreteValuationRing [Fact (2 * a ≠ 0)] : IsDiscreteValuationRing (LocalRing K t a ha) := by
  apply ((IsDiscreteValuationRing.TFAE (LocalRing K t a ha) (localRing_not_isField K t a ha Fact.out)).out 0 4).mpr
  rw [maximalIdeal_eq_span_parameter K t a ha Fact.out]
  infer_instance

theorem parameter_irreducible [Fact (2 * a ≠ 0)] : Irreducible (parameter K t a ha) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (maximalIdeal_eq_span_parameter K t a ha Fact.out)

end MazurTransfer.Order13OrdinaryDiscreteValuationRing
#print axioms MazurTransfer.Order13OrdinaryDiscreteValuationRing.parameter_ne_zero
#print axioms MazurTransfer.Order13OrdinaryDiscreteValuationRing.parameter_irreducible


