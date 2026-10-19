-- Prove2me | Definitions.Def_MazurTransfer_Order13OrdinaryFunctionFieldAndCuspCentersOriginalDataAndCertificates20261018
-- name    : MazurTransfer_Order13OrdinaryFunctionFieldAndCuspCentersOriginalDataAndCertificates20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T19:08:43.103643+00:00
-- url     : https://prove2.me/theorems/0640ad23-82ac-4dae-b51d-645ae15f4740
-- title:
--   Original ordinary function-field embeddings and rational cusp centers
-- statement:
--   Retain the original ordinary localization embeddings into the actual curve function field, their canonical scalar algebra and fraction-ring certificates, the ordinary place order formulas, classification of the four cusp primes, and identification with the literal rational section centers. All thirty complete original declaration types and all seven nonproof values, including the scalar-algebra constructor, are compared, together with four original field fact-provider types. Named downstream consumers are the actual cubic cusp valuations and the global cubic-divisor support calculation.
-- source:
--   Original retained MazurTheorem ordinary chart, place-order, cusp-prime and section-center modules, Apache-2.0, Vas and contributors. This packages existing checked constructors and their proved certificates, with complete original type and whole nonproof value comparisons.

import Mathlib
import Definitions.Def_MazurTransfer_Order13OrdinaryLocalOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_Order13CubicNormChartOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_AffineChartLocalStalkData
import Definitions.Def_MazurTransfer_Order13ActualRationalSectionDegreeOneData
import Definitions.Def_MazurTransfer_Order13ChartOverlapEmbeddingData
import Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldStalk_local_stalk_coordinate_commutes
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_neg_log_of_valuationSubring_eq
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original ordinary localization embeddings into the actual function field, valuation orders, classification of the ordinary cusp primes, and identification with the literal section centers. Named downstream consumers: Order13CubicActualCuspValuations and Order13CubicGlobalSupport in the cubic principal-divisor calculation. All original fields, characteristic, nonzero tangent and section hypotheses are retained.
-/
universe u
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual ordinary chart evaluation localizations
embed in the existing scheme function field, as fraction-ring bases.
Named downstream consumer: the cubic functions' actual finite cusp valuations.
The embeddings come from the literal chart open immersion.
-/

noncomputable section
namespace MazurTransfer.Order13OrdinaryChartActualFunctionField
open AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13OrdinaryLocalParameter
variable (K : Type u) [Field K] [CharZero K]
local instance order13OrdinaryChartActualFunctionFieldOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩

theorem primeCompl_image_isUnit (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t)
    (b : (pointIdeal K t a ha).primeCompl) :
    IsUnit (algebraMap (CoordinateRing K) (actualCurveFunctionField K) b) := by
  apply isUnit_iff_ne_zero.mpr
  apply (map_ne_zero_iff _ (IsFractionRing.injective (CoordinateRing K)
    (actualCurveFunctionField K))).mpr
  intro hb
  apply b.2
  rw [hb]
  exact Ideal.zero_mem _

def localEmbedding (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) :
    LocalRing K t a ha →+* actualCurveFunctionField K :=
  IsLocalization.lift (S := LocalRing K t a ha) (primeCompl_image_isUnit K t a ha)

instance localFunctionFieldAlgebra (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) :
    Algebra (LocalRing K t a ha) (actualCurveFunctionField K) := (localEmbedding K t a ha).toAlgebra

theorem localEmbedding_coordinate (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) (b : CoordinateRing K) :
    localEmbedding K t a ha (algebraMap (CoordinateRing K) (LocalRing K t a ha) b) =
      algebraMap (CoordinateRing K) (actualCurveFunctionField K) b :=
  IsLocalization.lift_eq (primeCompl_image_isUnit K t a ha) b

instance coordinateLocalFunctionField_isScalarTower (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) :
    IsScalarTower (CoordinateRing K) (LocalRing K t a ha) (actualCurveFunctionField K) :=
  IsScalarTower.of_algebraMap_eq fun b => (localEmbedding_coordinate K t a ha b).symm

instance localFunctionField_isFractionRing (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) :
    IsFractionRing (LocalRing K t a ha) (actualCurveFunctionField K) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (pointIdeal K t a ha).primeCompl (LocalRing K t a ha) (actualCurveFunctionField K)

end MazurTransfer.Order13OrdinaryChartActualFunctionField
#print axioms MazurTransfer.Order13OrdinaryChartActualFunctionField.localEmbedding_coordinate
#print axioms MazurTransfer.Order13OrdinaryChartActualFunctionField.localFunctionField_isFractionRing

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: ordinary evaluation localizations with 2a nonzero define
genuine places of the literal rational function field, with x-t of order one.
Named downstream consumer: finite cusp orders of the cubic principal divisor.
-/

noncomputable section
namespace MazurTransfer.Order13OrdinaryActualPlaceOrders
open AlgebraicGeometry AlgebraicCurve IsDedekindDomain WithZero
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13OrdinaryLocalParameter Order13OrdinaryChartActualFunctionField
local instance order13OrdinaryActualPlaceOrdersOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

def ordinaryPlace (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)] : Place ℚ (actualCurveFunctionField ℚ) :=
  Place.ofHeightOneSpectrum (IsDiscreteValuationRing.maximalIdeal (LocalRing ℚ t a ha))

def rawValuation (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)] : Valuation (actualCurveFunctionField ℚ) ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal (LocalRing ℚ t a ha)).valuation (actualCurveFunctionField ℚ)

theorem rawValuation_parameter (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)] :
    rawValuation t a ha (algebraMap (LocalRing ℚ t a ha) (actualCurveFunctionField ℚ) (parameter ℚ t a ha)) =
      exp (-1 : ℤ) := by
  rw [rawValuation, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _
    (Order13OrdinaryDiscreteValuationRing.parameter_ne_zero ℚ t a ha)
    (Order13OrdinaryLocalParameter.maximalIdeal_eq_span_parameter ℚ t a ha Fact.out)

theorem rawValuation_isUnit (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)]
    (b : LocalRing ℚ t a ha) (hb : IsUnit b) :
    rawValuation t a ha (algebraMap (LocalRing ℚ t a ha) (actualCurveFunctionField ℚ) b) = 1 := by
  rw [rawValuation, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff]
  change b ∉ IsLocalRing.maximalIdeal (LocalRing ℚ t a ha)
  simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hb

theorem ord_algebraMap (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)]
    (b : LocalRing ℚ t a ha) (hb : b ≠ 0) :
    (ordinaryPlace t a ha).ord (algebraMap (LocalRing ℚ t a ha) (actualCurveFunctionField ℚ) b) =
      -log (rawValuation t a ha (algebraMap (LocalRing ℚ t a ha) (actualCurveFunctionField ℚ) b)) :=
  Place.ord_eq_neg_log_of_valuationSubring_eq (ordinaryPlace t a ha) (rawValuation t a ha) rfl
    (rawValuation_parameter t a ha) ((map_ne_zero_iff _
      (IsFractionRing.injective (LocalRing ℚ t a ha) (actualCurveFunctionField ℚ))).mpr hb)

theorem ordinaryPlace_ord_parameter (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)] :
    (ordinaryPlace t a ha).ord (algebraMap (LocalRing ℚ t a ha) (actualCurveFunctionField ℚ) (parameter ℚ t a ha)) = 1 := by
  rw [ord_algebraMap t a ha _ (Order13OrdinaryDiscreteValuationRing.parameter_ne_zero ℚ t a ha),
    rawValuation_parameter, log_exp]
  norm_num

theorem ordinaryPlace_ord_isUnit (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)]
    (b : LocalRing ℚ t a ha) (hb : IsUnit b) :
    (ordinaryPlace t a ha).ord (algebraMap (LocalRing ℚ t a ha) (actualCurveFunctionField ℚ) b) = 0 := by
  rw [ord_algebraMap t a ha b hb.ne_zero, rawValuation_isUnit t a ha b hb, log_one, neg_zero]

theorem ordinaryPlace_ord_associated_parameter_pow (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)]
    (b : LocalRing ℚ t a ha) (n : ℕ) (hb : Associated b (parameter ℚ t a ha ^ n)) :
    (ordinaryPlace t a ha).ord (algebraMap (LocalRing ℚ t a ha) (actualCurveFunctionField ℚ) b) = n := by
  have hb0 := hb.ne_zero_iff.mpr (pow_ne_zero n (Order13OrdinaryDiscreteValuationRing.parameter_ne_zero ℚ t a ha))
  obtain ⟨u, hu⟩ := hb
  let φ : LocalRing ℚ t a ha →+* actualCurveFunctionField ℚ := algebraMap _ _
  let v := ordinaryPlace t a ha
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hzord : v.ord (φ (parameter ℚ t a ha)) = 1 := ordinaryPlace_ord_parameter t a ha
  calc
    v.ord (φ b) = v.ord (φ (b * (u : LocalRing ℚ t a ha))) := by
      rw [map_mul, v.ord_mul ((map_ne_zero_iff φ hinj).mpr hb0)
        ((map_ne_zero_iff φ hinj).mpr u.ne_zero), ordinaryPlace_ord_isUnit t a ha _ u.isUnit,
        add_zero]
    _ = v.ord (φ (parameter ℚ t a ha ^ n)) := congrArg (fun x => v.ord (φ x)) hu
    _ = n := by
      rw [map_pow, ← zpow_natCast, v.ord_zpow, hzord, mul_one]


end MazurTransfer.Order13OrdinaryActualPlaceOrders
#print axioms MazurTransfer.Order13OrdinaryActualPlaceOrders.ordinaryPlace_ord_parameter
#print axioms MazurTransfer.Order13OrdinaryActualPlaceOrders.ordinaryPlace_ord_associated_parameter_pow

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: primes in the literal ordinary chart with x=0 or x=-1
are exactly the evaluation primes at the four ordinary cusps. Named
 downstream consumer: the complete cubic principal-divisor support.
-/

noncomputable section
namespace MazurTransfer.Order13OrdinaryCuspPrimeClassification
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open Order13IntegralSections
variable (K : Type u) [Field K]

theorem evaluation_const (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t) (r : K) :
    ordinaryEvaluation K t a ha (algebraMap K (CoordinateRing K) r) = r :=
  RingHom.congr_fun (ordinaryEvaluation_comp_algebraMap K t a ha) r

theorem prime_eq_evaluation_kernel (p : PrimeSpectrum (CoordinateRing K))
    (t a : K) (ha : a ^ 2 = (sexticPolynomial K).eval t)
    (hx : xCoordinate K - algebraMap K (CoordinateRing K) t ∈ p.asIdeal)
    (hy : yCoordinate K - algebraMap K (CoordinateRing K) a ∈ p.asIdeal) :
    p.asIdeal = RingHom.ker (ordinaryEvaluation K t a ha) := by
  haveI : p.asIdeal.IsPrime := p.isPrime
  let q := Ideal.Quotient.mk p.asIdeal
  let c := q.comp (algebraMap K (CoordinateRing K))
  let e := ordinaryEvaluation K t a ha
  have hxq : q (xCoordinate K) = c t := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    change q (xCoordinate K - algebraMap K (CoordinateRing K) t) = 0 at h
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  have hyq : q (yCoordinate K) = c a := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hy
    change q (yCoordinate K - algebraMap K (CoordinateRing K) a) = 0 at h
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  have hq : q = c.comp e := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext'
      · apply RingHom.ext
        intro r
        change q (algebraMap K (CoordinateRing K) r) = c (e (algebraMap K (CoordinateRing K) r))
        rw [evaluation_const]
        rfl
      · change q (xCoordinate K) = c (e (xCoordinate K))
        rw [ordinaryEvaluation_x]
        exact hxq
    · change q (yCoordinate K) = c (e (yCoordinate K))
      rw [ordinaryEvaluation_y]
      exact hyq
  ext b
  change b ∈ p.asIdeal ↔ e b = 0
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change q b = 0 ↔ e b = 0
  rw [hq, RingHom.comp_apply]
  exact map_eq_zero_iff c c.injective

theorem y_sign_at_x (p : PrimeSpectrum (CoordinateRing K)) (t : K)
    (hx : xCoordinate K - algebraMap K (CoordinateRing K) t ∈ p.asIdeal)
    (ht : (sexticPolynomial K).eval t = 1) :
    yCoordinate K - 1 ∈ p.asIdeal ∨ yCoordinate K + 1 ∈ p.asIdeal := by
  haveI : p.asIdeal.IsPrime := p.isPrime
  let q := Ideal.Quotient.mk p.asIdeal
  have hxq : q (xCoordinate K) = q (algebraMap K (CoordinateRing K) t) := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    change q (xCoordinate K - algebraMap K (CoordinateRing K) t) = 0 at h
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  have hs : q (yCoordinate K) ^ 2 = 1 := by
    have h := congrArg q (yCoordinate_sq K)
    have heval : q ((sexticPolynomial K).aeval (xCoordinate K)) =
        q (algebraMap K (CoordinateRing K) ((sexticPolynomial K).eval t)) := by
      simp only [sexticPolynomial, map_add, map_mul, map_pow, map_ofNat, map_one, aeval_X, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one]
      rw [hxq]
    rw [map_pow, heval, ht, map_one] at h
    exact h
  have hm : (q (yCoordinate K) - 1) * (q (yCoordinate K) + 1) = 0 := by
    calc
      _ = q (yCoordinate K) ^ 2 - 1 := by ring
      _ = 0 := by rw [hs]; ring
  rcases mul_eq_zero.mp hm with h | h
  · left
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_sub, map_one] using h
  · right
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_add, map_one] using h

theorem prime_at_zero (p : PrimeSpectrum (CoordinateRing K)) (hx : xCoordinate K ∈ p.asIdeal) :
    p.asIdeal = RingHom.ker (ordinaryEvaluation K 0 1 (by rw [sextic_eval_zero]; simp)) ∨
    p.asIdeal = RingHom.ker (ordinaryEvaluation K 0 (-1) (by rw [sextic_eval_zero]; simp)) := by
  have hx' : xCoordinate K - algebraMap K (CoordinateRing K) 0 ∈ p.asIdeal := by simpa using hx
  rcases y_sign_at_x K p 0 hx' (sextic_eval_zero K) with hy | hy
  · left
    apply prime_eq_evaluation_kernel K p 0 1 _ hx'
    simpa only [map_one] using hy
  · right
    apply prime_eq_evaluation_kernel K p 0 (-1) _ hx'
    simpa only [map_neg, map_one, sub_neg_eq_add] using hy

theorem prime_at_neg_one (p : PrimeSpectrum (CoordinateRing K)) (hx : xCoordinate K + 1 ∈ p.asIdeal) :
    p.asIdeal = RingHom.ker (ordinaryEvaluation K (-1) 1 (by rw [sextic_eval_neg_one]; simp)) ∨
    p.asIdeal = RingHom.ker (ordinaryEvaluation K (-1) (-1) (by rw [sextic_eval_neg_one]; simp)) := by
  have hx' : xCoordinate K - algebraMap K (CoordinateRing K) (-1) ∈ p.asIdeal := by
    simpa only [map_neg, map_one, sub_neg_eq_add] using hx
  rcases y_sign_at_x K p (-1) hx' (sextic_eval_neg_one K) with hy | hy
  · left
    apply prime_eq_evaluation_kernel K p (-1) 1 _ hx'
    simpa only [map_one] using hy
  · right
    apply prime_eq_evaluation_kernel K p (-1) (-1) _ hx'
    simpa only [map_neg, map_one, sub_neg_eq_add] using hy

end MazurTransfer.Order13OrdinaryCuspPrimeClassification
#print axioms MazurTransfer.Order13OrdinaryCuspPrimeClassification.prime_at_zero
#print axioms MazurTransfer.Order13OrdinaryCuspPrimeClassification.prime_at_neg_one

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the four ordinary evaluation primes are the literal
rational cusp section centers. Named downstream consumer: global support
of the cubic principal divisor.
-/

noncomputable section
namespace MazurTransfer.Order13OrdinaryCuspCenters
open AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open Order13IntegralSections Order13RationalSectionPicardInjection
open Order13OrdinaryCuspPrimeClassification
local instance order13OrdinaryCuspCentersOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

def ordinaryChartPoint (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) :
    Spec (.of (CoordinateRing ℚ)) := ⟨RingHom.ker (ordinaryEvaluation ℚ t a ha), RingHom.ker_isPrime _⟩

theorem ordinary_section_center (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) :
    (sectionClosedPoint ℚ (ordinarySection ℚ t a ha)).1 = ordinaryChartMap ℚ (ordinaryChartPoint t a ha) := by
  change ordinaryChartMap ℚ ((Spec.map (CommRingCat.ofHom (ordinaryEvaluation ℚ t a ha)))
      (IsLocalRing.closedPoint ℚ)) = ordinaryChartMap ℚ (ordinaryChartPoint t a ha)
  apply congrArg (ordinaryChartMap ℚ)
  apply PrimeSpectrum.ext
  change Ideal.comap (ordinaryEvaluation ℚ t a ha) (IsLocalRing.maximalIdeal ℚ) = RingHom.ker (ordinaryEvaluation ℚ t a ha)
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

theorem point_with_zero_x (p : Spec (.of (CoordinateRing ℚ))) (hx : xCoordinate ℚ ∈ p.asIdeal) :
    ordinaryChartMap ℚ p = (sectionClosedPoint ℚ (zeroPositiveSection ℚ)).1 ∨
    ordinaryChartMap ℚ p = (sectionClosedPoint ℚ (zeroNegativeSection ℚ)).1 := by
  rcases prime_at_zero ℚ p hx with hp | hp
  · left
    rw [zeroPositiveSection, ordinary_section_center]
    apply congrArg (ordinaryChartMap ℚ)
    exact PrimeSpectrum.ext hp
  · right
    rw [zeroNegativeSection, ordinary_section_center]
    apply congrArg (ordinaryChartMap ℚ)
    exact PrimeSpectrum.ext hp

theorem point_with_neg_one_x (p : Spec (.of (CoordinateRing ℚ))) (hx : xCoordinate ℚ + 1 ∈ p.asIdeal) :
    ordinaryChartMap ℚ p = (sectionClosedPoint ℚ (negOnePositiveSection ℚ)).1 ∨
    ordinaryChartMap ℚ p = (sectionClosedPoint ℚ (negOneNegativeSection ℚ)).1 := by
  rcases prime_at_neg_one ℚ p hx with hp | hp
  · left
    rw [negOnePositiveSection, ordinary_section_center]
    apply congrArg (ordinaryChartMap ℚ)
    exact PrimeSpectrum.ext hp
  · right
    rw [negOneNegativeSection, ordinary_section_center]
    apply congrArg (ordinaryChartMap ℚ)
    exact PrimeSpectrum.ext hp

end MazurTransfer.Order13OrdinaryCuspCenters
#print axioms MazurTransfer.Order13OrdinaryCuspCenters.point_with_zero_x
#print axioms MazurTransfer.Order13OrdinaryCuspCenters.point_with_neg_one_x

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify ordinary-localization places with the canonical
places centered at literal rational ordinary sections. Named downstream
consumer: actual finite cusp valuations and the cubic principal divisor.
The actual stalk diagram supplies the identification, rather than a supplied
valuation equivalence or a substituted abstract curve.
-/

noncomputable section
namespace MazurTransfer.Order13ActualOrdinaryPlaceCenters
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13OrdinaryLocalParameter Order13OrdinaryChartActualFunctionField
open Order13OrdinaryActualPlaceOrders Order13IntegralSections
open Order13RationalSectionPicardInjection
local instance order13ActualOrdinaryPlaceCentersOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13OrdinaryCuspCenters

def center (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)] : curveScheme ℚ :=
  ordinaryChartMap ℚ (ordinaryChartPoint t a ha)

def localStalkIso (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)] :
    CommRingCat.of (LocalRing ℚ t a ha) ≅ (curveScheme ℚ).presheaf.stalk (center t a ha) :=
  AffineOpenChartFunctionFieldStalk.localStalkIso (.of (CoordinateRing ℚ))
    (ordinaryChartMap ℚ) (ordinaryChartPoint t a ha)

theorem localEmbedding_eq_stalk (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)] :
    localEmbedding ℚ t a ha =
      (algebraMap ((curveScheme ℚ).presheaf.stalk (center t a ha)) (actualCurveFunctionField ℚ)).comp
        (localStalkIso t a ha).hom.hom := by
  apply IsLocalization.ringHom_ext (pointIdeal ℚ t a ha).primeCompl
  have H := AffineOpenChartFunctionFieldStalk.local_stalk_coordinate_commutes
    (.of (CoordinateRing ℚ)) (ordinaryChartMap ℚ) (ordinaryChartPoint t a ha)
  apply RingHom.ext
  intro b
  rw [RingHom.comp_apply, localEmbedding_coordinate]
  exact congrArg (fun f => f.hom b) H

theorem localEmbedding_range_eq_stalk (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)] :
    (localEmbedding ℚ t a ha).range =
      (algebraMap ((curveScheme ℚ).presheaf.stalk (center t a ha)) (actualCurveFunctionField ℚ)).range := by
  rw [localEmbedding_eq_stalk]
  ext f
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨(localStalkIso t a ha).hom b, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (localStalkIso t a ha).hom).2 b
    exact ⟨c, rfl⟩

theorem localEmbedding_range_eq_place (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)] :
    (localEmbedding ℚ t a ha).range = (ordinaryPlace t a ha).toValuationSubring.toSubring := by
  change (algebraMap (LocalRing ℚ t a ha) (actualCurveFunctionField ℚ)).range = _
  rw [RingHom.range_eq_map]
  exact IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
    (A := LocalRing ℚ t a ha) (K := actualCurveFunctionField ℚ)

theorem ordinaryPlace_eq_actualPlaceOfPoint (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)] :
    ordinaryPlace t a ha = actualPlaceOfPoint ℚ (sectionClosedPoint ℚ (ordinarySection ℚ t a ha)) := by
  apply Place.ext
  apply ValuationSubring.toSubring_injective
  rw [← localEmbedding_range_eq_place, localEmbedding_range_eq_stalk,
    center, ← ordinary_section_center, actualPlaceOfPoint_stalk_range]

theorem ordinaryPlace_deg (t a : ℚ) (ha : a ^ 2 = (sexticPolynomial ℚ).eval t) [Fact (2 * a ≠ 0)] : (ordinaryPlace t a ha).deg = 1 := by
  rw [ordinaryPlace_eq_actualPlaceOfPoint]
  exact (sectionDegreeOneClosedPoint ℚ (ordinarySection ℚ t a ha)).2


end MazurTransfer.Order13ActualOrdinaryPlaceCenters
#print axioms MazurTransfer.Order13ActualOrdinaryPlaceCenters.ordinaryPlace_eq_actualPlaceOfPoint
#print axioms MazurTransfer.Order13ActualOrdinaryPlaceCenters.ordinaryPlace_deg


