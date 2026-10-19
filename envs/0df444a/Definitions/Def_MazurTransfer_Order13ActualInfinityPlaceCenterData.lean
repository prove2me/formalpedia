-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualInfinityPlaceCenterData
-- name    : MazurTransfer_Order13ActualInfinityPlaceCenterData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T13:02:16.802189+00:00
-- url     : https://prove2.me/theorems/945dfebc-3773-4610-ba15-2a7224df13f6
-- title:
--   Actual reciprocal infinity chart points, centers and local-stalk isomorphisms
-- statement:
--   For $a\in\mathbb Q$ with $a^2=1$, the original reciprocal evaluation kernel defines the specified chart point and its actual image $x_a$ on the literal curve. The original local-stalk isomorphism is $$A_{\mathfrak m_a}\simeq\mathcal O_{C,x_a}.$$ These three exact constructors supply the actual local-embedding/stalk comparison and canonical infinity-place identification.
-- source:
--   Original complete chartPoint, center and localStalkIso declarations and bodies from MazurTheorem Order13ActualInfinityPlaceCenters.lean, Apache-2.0, Vas and contributors. Three complete original closed types and three data values are kernel-compared. Public imports alone replace dependencies. The checked source gives the explicit constructor boundary and named downstream consumer: actual local-embedding/stalk comparison and canonical section centers.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the two reciprocal-localization places with the
canonical places centered at the two literal rational infinity sections.
Named downstream consumer: the actual degree-19 Pell principal divisor.
The actual stalk diagram supplies the identification, rather than a supplied
valuation equivalence or a substituted abstract curve.
-/
/- Design boundary: the actual reciprocal infinity chart point, center and local-stalk isomorphism.
Named downstream consumer: actual infinity local-embedding/stalk comparison. -/
import Definitions.Def_MazurTransfer_Order13ActualInfinityValuationData
import Definitions.Def_MazurTransfer_AffineChartLocalStalkData
noncomputable section
namespace MazurTransfer.Order13ActualInfinityPlaceCenters
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityLocalParameter Order13ReciprocalChartActualFunctionField
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
def chartPoint (a : ℚ) (ha : a ^ 2 = 1) : Spec (.of (ReciprocalRing ℚ)) :=
  ⟨infinityIdeal ℚ a ha, inferInstance⟩

def center (a : ℚ) (ha : a ^ 2 = 1) : curveScheme ℚ :=
  reciprocalChartMap ℚ (chartPoint a ha)

def localStalkIso (a : ℚ) (ha : a ^ 2 = 1) :
    CommRingCat.of (LocalRing ℚ a ha) ≅ (curveScheme ℚ).presheaf.stalk (center a ha) :=
  AffineOpenChartFunctionFieldStalk.localStalkIso (.of (ReciprocalRing ℚ))
    (reciprocalChartMap ℚ) (chartPoint a ha)

end MazurTransfer.Order13ActualInfinityPlaceCenters
#print axioms MazurTransfer.Order13ActualInfinityPlaceCenters.localStalkIso


