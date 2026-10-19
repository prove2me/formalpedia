-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalWholeGenericFibreIsomorphismData20261019
-- name    : MazurTransfer_Order13ActualDyadicOriginalWholeGenericFibreIsomorphismData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T05:16:53.005666+00:00
-- url     : https://prove2.me/theorems/5dec613a-d513-475c-a34e-83757b8f3d03
-- title:
--   Original chosen whole dyadic generic-fibre isomorphism
-- statement:
--   The exact original whole generic-fibre isomorphism for the actual dyadic mixed quadratic curve, obtained by composing its chosen whole coefficient-base-change isomorphism with its chosen rational curve isomorphism. Two original full types, the whole chosen isomorphism value and its original prime-provider type are checked. The inverse respects the projection to Spec Q. Named downstream consumer: the actual smooth proper dyadic model and its compatible Picard family.
-- source:
--   MazurTheorem original mixed quadratic integral charts, overlap and gluing, by Vasily Ilin and contributors; Apache-2.0. Original attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the actual WHOLE generic fibre of the smooth
proper mixed quadratic Z_(2)-family with the SAME existing rational curve,
over Spec Q. Named downstream consumer: good reduction at two and the
compatible integral Picard and norm families. Picard data are separate.
-/
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeRationalCurveComparisonData20261019

noncomputable section
namespace MazurTransfer.Order13ActualDyadicMixedQuadraticGenericFibre
open Polynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedQuadraticActualCurveBaseChange Order13MixedQuadraticWholeCurveComparisonOverBase
theorem originalDyadicGenericFibrePrimeProvider20261019 : Fact (Nat.Prime 2) := ⟨by decide⟩
attribute [local instance] originalDyadicGenericFibrePrimeProvider20261019

def dyadicGenericFibreIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap BaseRing ℚ))) (curveToBase BaseRing) ≅
      MazurTorsion.XOneThirteenProjectiveCurve.curveScheme ℚ :=
  (wholeCurveBaseChangeIso BaseRing ℚ).trans rationalCurveIso

theorem dyadicGenericFibreIso_inv_fst :
    dyadicGenericFibreIso.inv ≫ pullback.fst _ _ =
      MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ := by
  change (rationalCurveIso.inv ≫ (wholeCurveBaseChangeIso BaseRing ℚ).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, wholeCurveBaseChangeIso_inv_fst]
  exact wholeCurveIso_inv_toBase ℚ (C ((1 : ℚ) / 2))
    Order13MixedQuadraticRationalChartComparison.rational_two_inverse

end MazurTransfer.Order13ActualDyadicMixedQuadraticGenericFibre
#print axioms MazurTransfer.Order13ActualDyadicMixedQuadraticGenericFibre.dyadicGenericFibreIso
#print axioms MazurTransfer.Order13ActualDyadicMixedQuadraticGenericFibre.dyadicGenericFibreIso_inv_fst


