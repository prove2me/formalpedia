-- Prove2me | Definitions.Def_MazurTransfer_Order13CanonicalInfinityPellOrders
-- name    : MazurTransfer_Order13CanonicalInfinityPellOrders
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T13:21:59.934182+00:00
-- url     : https://prove2.me/theorems/8d2bebe7-c8fa-493c-8eb1-da14dd529e87
-- title:
--   Canonical infinity section places have degree one and Pell orders minus nineteen and nineteen
-- statement:
--   The two literal rational infinity sections give canonical places of degree one. For the explicit Pell function $f$, their orders are $$\operatorname{ord}_{\infty_+}(f)=-19,\qquad\operatorname{ord}_{\infty_-}(f)=19.$$ In particular the two sections are distinct. These original certificates connect the local calculation to the global Pell divisor.
-- source:
--   Original complete infinityPlace_deg, canonical_positive_infinity_pell_ord, canonical_negative_infinity_pell_ord and negative_infinity_section_ne_positive declarations and bodies from MazurTheorem Order13ActualInfinityPlaceCenters.lean, Apache-2.0, Vas and contributors. Four complete original closed types are kernel-compared. Public proved imports supply dependencies. Named downstream consumer: actual global Pell principal divisor.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the two reciprocal-localization places with the
canonical places centered at the two literal rational infinity sections.
Named downstream consumer: the actual degree-19 Pell principal divisor.
The actual stalk diagram supplies the identification, rather than a supplied
valuation equivalence or a substituted abstract curve.
-/
/- Scope: the original four degree and canonical infinity-order certificates only. -/
import Definitions.Def_MazurTransfer_Order13ActualInfinitySectionCenterCertificates
import Theorems.Thm_MazurTransfer_Order13ActualInfinityPlaceCenters_infinityPlace_eq_actualPlaceOfPoint
import Theorems.Thm_MazurTransfer_Order13PellActualInfinityValuations_pellFunction_ord_at_positive
import Theorems.Thm_MazurTransfer_Order13PellActualInfinityValuations_pellFunction_ord_at_negative
noncomputable section
namespace MazurTransfer.Order13ActualInfinityPlaceCenters
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityLocalParameter Order13ReciprocalChartActualFunctionField
open Order13PellActualInfinityValuations Order13IntegralSections
open Order13RationalSectionPicardInjection
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem infinityPlace_deg (a : ℚ) (ha : a ^ 2 = 1) : (infinityPlace a ha).deg = 1 := by
  rw [infinityPlace_eq_actualPlaceOfPoint]
  exact (sectionDegreeOneClosedPoint ℚ (infinitySection ℚ a ha)).2

theorem canonical_positive_infinity_pell_ord :
    (actualPlaceOfPoint ℚ (sectionClosedPoint ℚ (positiveInfinitySection ℚ))).ord pellFunction = -19 := by
  exact (congrArg (fun v => v.ord pellFunction)
    (infinityPlace_eq_actualPlaceOfPoint 1 (Order13PellInfinityLocalOrders.positiveProof ℚ))).symm.trans
      pellFunction_ord_at_positive

theorem canonical_negative_infinity_pell_ord :
    (actualPlaceOfPoint ℚ (sectionClosedPoint ℚ (negativeInfinitySection ℚ))).ord pellFunction = 19 := by
  exact (congrArg (fun v => v.ord pellFunction)
    (infinityPlace_eq_actualPlaceOfPoint (-1) (Order13PellInfinityLocalOrders.negativeProof ℚ))).symm.trans
      pellFunction_ord_at_negative

theorem negative_infinity_section_ne_positive :
    negativeInfinitySection ℚ ≠ positiveInfinitySection ℚ := by
  intro h
  have hn := canonical_negative_infinity_pell_ord
  rw [h, canonical_positive_infinity_pell_ord] at hn
  norm_num at hn

end MazurTransfer.Order13ActualInfinityPlaceCenters
#print axioms MazurTransfer.Order13ActualInfinityPlaceCenters.infinityPlace_deg
#print axioms MazurTransfer.Order13ActualInfinityPlaceCenters.canonical_positive_infinity_pell_ord
#print axioms MazurTransfer.Order13ActualInfinityPlaceCenters.canonical_negative_infinity_pell_ord
#print axioms MazurTransfer.Order13ActualInfinityPlaceCenters.negative_infinity_section_ne_positive


