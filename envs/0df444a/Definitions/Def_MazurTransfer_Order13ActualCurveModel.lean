-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualCurveModel
-- name    : MazurTransfer_Order13ActualCurveModel
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T03:00:35.954702+00:00
-- url     : https://prove2.me/theorems/16e581cf-f376-443e-bd42-9805d4736e8c
-- title:
--   The actual order-thirteen curve as a model of its function field
-- statement:
--   Let $K$ be a field with $104\ne0$, let $C_K$ be the fixed smooth proper order-thirteen curve, and let $F=K(C_K)$ be its actual function field. This interface constructs the curve model
--   $$\bigl(C_K\longrightarrow\operatorname{Spec}K,\;K(C_K)\cong F\bigr),$$
--   including the actual closed-point/place bijection, its local-stalk valuation-ring identity, and affine neighborhoods for all finite sets of points.
--
--   The constructor uses the actual curve, actual structure map and identity function-field isomorphism. The two nontrivial support results are separate proved public theorems. This model is the input to the actual literal-curve point-difference injection used in integral Abel–Jacobi injectivity.
-- source:
--   Unchanged constructor body from checked MazurTheorem source Order13ActualArithmeticCurveModel.lean, selected by the Lean declaration and syntax oracles. The closed-point/place bijection and finite-set affine-neighborhood facts are Proved public theorem inputs. All three original constructor and projection types are compared by closed kernel witnesses. Vas and contributors, Apache-2.0; official Anthropic FLT APIs retain Apache-2.0 and pin 6e837e75355538c7f80bab5b956861e86c4eacc2.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original literal good-characteristic curve and its actual
function field form a CurveModel. Named downstream consumer: the actual
literal curve point-difference injection in the integral Abel-Jacobi proof.
The constructor body is unchanged from Order13ActualArithmeticCurveModel.lean.
The place bijection and finite-set affine-neighborhood results are separate
Proved public theorem inputs. Official Anthropic FLT APIs retain Apache-2.0
and pin 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
import Theorems.Thm_MazurTransfer_order13_actual_place_of_point_bijective
import Theorems.Thm_MazurTransfer_Order13ActualArithmeticCurveModel_finset_contained_affine_open
noncomputable section
universe u
namespace GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]
theorem actualPlaceOfPoint_bijective : Function.Bijective (actualPlaceOfPoint K) :=
  _root_.MazurTransfer.order13_actual_place_of_point_bijective K
end GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
namespace MazurTransfer.Order13ActualArithmeticCurveModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]
def actualCurveModel : CurveModel K (actualCurveFunctionField K) where
  C := curveScheme K
  toBase := curveToBase K
  ffEquiv := RingEquiv.refl _
  ffEquiv_algebraMap := fun _ => rfl
  placeOfPoint := actualPlaceOfPoint K
  placeOfPoint_bijective := actualPlaceOfPoint_bijective K
  range_stalk_eq := fun x => by
    rw [← actualPlaceOfPoint_stalk_range K x]
    ext f
    simp
  finset_subset_affineOpen := finset_contained_affine_open K
@[simp] theorem actualCurveModel_scheme : (actualCurveModel K).C = curveScheme K := rfl
@[simp] theorem actualCurveModel_structure : (actualCurveModel K).toBase = curveToBase K := rfl
end MazurTransfer.Order13ActualArithmeticCurveModel
#print axioms MazurTransfer.Order13ActualArithmeticCurveModel.actualCurveModel


