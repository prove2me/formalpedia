-- Prove2me | Definitions.Def_MazurTransfer_Order13PellPrincipalDivisorData
-- name    : MazurTransfer_Order13PellPrincipalDivisorData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T13:26:10.088898+00:00
-- url     : https://prove2.me/theorems/cc601c92-33b3-43c4-b0fa-9b735f0aaed0
-- title:
--   The actual canonical infinity places and the explicit Pell two-point divisor
-- statement:
--   On the literal order-13 curve over $\mathbb Q$, let $v_+$ and $v_-$ be the canonical places of its positive and negative infinity sections. These are distinct, and the specified Pell divisor is $$D=19[v_-]-19[v_+].$$ This library records the actual places and original divisor constructor for the global principal-divisor certificate.
-- source:
--   Original complete positivePlace, negativePlace, negativePlace_ne_positivePlace and pellDivisor declarations and bodies from MazurTheorem Order13PellPrincipalDivisor.lean, Apache-2.0, Vas and contributors. Four full original types and three data values are kernel-compared. Public canonical infinity-order certificates supply distinctness. Named downstream consumer: the actual Pell principal-divisor theorem.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact two-point principal divisor of the explicit Pell
function in the actual rational scheme function field. Named downstream
consumer: nineteen annihilates the difference of the infinity Picard classes.
-/
import Definitions.Def_MazurTransfer_Order13CanonicalInfinityPellOrders
noncomputable section
namespace MazurTransfer.Order13PellPrincipalDivisor
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13IntegralSections Order13RationalSectionPicardInjection Order13ActualInfinityPlaceCenters
open Order13PellActualInfinityValuations
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

def positivePlace : Place ℚ (actualCurveFunctionField ℚ) :=
  actualPlaceOfPoint ℚ (sectionClosedPoint ℚ (positiveInfinitySection ℚ))
def negativePlace : Place ℚ (actualCurveFunctionField ℚ) :=
  actualPlaceOfPoint ℚ (sectionClosedPoint ℚ (negativeInfinitySection ℚ))

theorem negativePlace_ne_positivePlace : negativePlace ≠ positivePlace := by
  intro H
  have Hp := canonical_positive_infinity_pell_ord
  have Hn := canonical_negative_infinity_pell_ord
  change positivePlace.ord pellFunction = -19 at Hp
  change negativePlace.ord pellFunction = 19 at Hn
  rw [H, Hp] at Hn
  norm_num at Hn

def pellDivisor : Divisor ℚ (actualCurveFunctionField ℚ) :=
  Finsupp.single negativePlace 19 - Finsupp.single positivePlace 19

end MazurTransfer.Order13PellPrincipalDivisor
#print axioms MazurTransfer.Order13PellPrincipalDivisor.positivePlace
#print axioms MazurTransfer.Order13PellPrincipalDivisor.negativePlace
#print axioms MazurTransfer.Order13PellPrincipalDivisor.negativePlace_ne_positivePlace
#print axioms MazurTransfer.Order13PellPrincipalDivisor.pellDivisor


