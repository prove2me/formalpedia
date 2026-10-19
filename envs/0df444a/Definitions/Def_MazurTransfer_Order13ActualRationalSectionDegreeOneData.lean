-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualRationalSectionDegreeOneData
-- name    : MazurTransfer_Order13ActualRationalSectionDegreeOneData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T12:58:26.442992+00:00
-- url     : https://prove2.me/theorems/99c0d82a-0a7a-4ded-b0ed-f43cfe034d0f
-- title:
--   Actual rational sections give literal degree-one closed points of the order-thirteen curve
-- statement:
--   Over every perfect field $K$ with $104\ne0$, each rational section of the literal order-thirteen curve determines its original closed point and a degree-one certificate for the corresponding actual function-field place: $$p\longmapsto x_p,\qquad \deg(v_{x_p})=1.$$ The four exact original constructors are retained. They supply canonical infinity centers and the actual Pell principal-divisor calculation.
-- source:
--   Original complete DegreeOneClosedPoint, ActualRationalSection, sectionClosedPoint and sectionDegreeOneClosedPoint declarations and bodies from MazurTheorem Order13ActualRationalClosedPointClassInjection.lean and Order13ActualRationalSectionPicardInjection.lean, Apache-2.0, Vas and contributors. Four complete original closed types and four data values are kernel-compared. The original Proved Anthropic FLT rationality-from-stalk-range and rationality/degree-one APIs at pin 6e837e75355538c7f80bab5b956861e86c4eacc2 are explicit imports. Design boundary: original section closed points and degree-one witnesses. Named downstream consumer: canonical infinity centers and actual Pell divisor.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Literal curve and rational-section dictionary: MazurTheorem WIP at
54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The pole and divisor-class
argument reuses official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2 with a checked perfect-field
Weil-canonical Riemann–Roch adaptation.
Design boundary: actual rational sections inject, via their closed points
and the class of P minus the actual (0,1) base point, into arithmetic Pic0.
Named downstream consumer: the rational-point obstruction after establishing
the rational Picard group and its reduction comparison. No finiteness or
rank-zero conclusion is asserted here.
-/
/- Design boundary: original actual rational-section closed points and degree-one certificates.
Named downstream consumer: identifying canonical infinity centers for the actual Pell divisor. -/
import Definitions.Def_MazurTransfer_RationalSectionClosedPointData
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
noncomputable section
universe u
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open NeronModelInfra MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
namespace MazurTransfer.Order13RationalClosedPointClassInjection
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
def DegreeOneClosedPoint :=
  {x : closedPoints (curveScheme K) // (actualPlaceOfPoint K x).deg = 1}

end MazurTransfer.Order13RationalClosedPointClassInjection
namespace MazurTransfer.Order13RationalSectionPicardInjection
open MazurTransfer.Order13RationalClosedPointClassInjection MazurTransfer.RigidFieldRationalSections
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
abbrev ActualRationalSection := SchemeHomOver (𝟙 (Spec (.of K))) (curveToBase K)

def sectionClosedPoint (p : ActualRationalSection K) : closedPoints (curveScheme K) :=
  ⟨pointOfSection (curveToBase K) p,
    mem_closedPoints_iff.mpr (sectionPoint_isClosed (curveToBase K) p)⟩

def sectionDegreeOneClosedPoint (p : ActualRationalSection K) : DegreeOneClosedPoint K := by
  refine ⟨sectionClosedPoint K p, ?_⟩
  apply ((actualPlaceOfPoint K (sectionClosedPoint K p)).isRational_iff_deg_eq_one).mp
  exact Place.isRational_of_range_stalk_section_eq (curveToBase K) p.1 p.2
    (actualPlaceOfPoint K (sectionClosedPoint K p))
    (actualPlaceOfPoint_stalk_range K (sectionClosedPoint K p))

end MazurTransfer.Order13RationalSectionPicardInjection
#print axioms MazurTransfer.Order13RationalSectionPicardInjection.sectionDegreeOneClosedPoint


