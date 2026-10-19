-- Prove2me | Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
-- name    : MazurTransfer_Order13GoodCharacteristicPlaceFoundation
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T02:45:34.47843+00:00
-- url     : https://prove2.me/theorems/d54e8e4a-39b7-400b-a9ac-1899a24fe55d
-- title:
--   Actual function field and closed-point places of the order-thirteen curve
-- statement:
--   Let $K$ be a field in which $104\ne0$, and let $C_K$ be the smooth proper curve obtained by gluing the two specified hyperelliptic charts of the order-thirteen model. This interface fixes its actual function field $K(C_K)$, its natural $K$-algebra structure, and a place $v_x$ for each closed point $x$ of $C_K$, characterized by
--   $$\operatorname{im}\bigl(\mathcal O_{C_K,x}\longrightarrow K(C_K)\bigr)=\mathcal O_{v_x}.$$
--
--   The geometry instances and the chosen-place constructor use the previously proved geometry of this same explicit curve. Bijectivity of the closed-point/place map is a separate theorem. This foundation supplies the actual CurveModel used by the Abel–Jacobi point-injection argument.
-- source:
--   Selected exact declarations from the checked MazurTheorem proof AcceptedOrder13GoodCharacteristicPicardCache.lean, source lines 70–251, extracted by the Lean declaration and syntax oracles. Unselected declarations are removed by skeleton subtraction. Selected declaration bodies and all 15 closed kernel types are preserved. Vas and contributors, Apache-2.0; official Anthropic FLT APIs at 6e837e75355538c7f80bab5b956861e86c4eacc2 retain their attribution.

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
Design boundary: actual good-characteristic represented Picard scheme and pointed
Abel-Jacobi morphism. Named downstream consumer: the finite-field divisor-class/
Jacobian point comparison for the order-13 campaign branch.
Full original Picard dependencies: official Anthropic FLT, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2. Actual curve: MazurTheorem,
54d43d8dda8a6fcf069cc02a815f850d762c5c0c. No Picard, group-law, finite-map,
or geometric-integrality assumption is added to the target.
-/
import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one




namespace GoodCharacteristicGeometryPublicProof


section
noncomputable section
open AlgebraicGeometry CategoryTheory
open _root_.MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13GoodCharacteristicGeometry
universe u
variable (K : Type u) [Field K] (h104 : (104 : K) ≠ 0)
include h104
theorem actual_good_characteristic_geometry :
    IsIntegral (curveScheme K) ∧ SmoothOfRelativeDimension 1 (curveToBase K) ∧
      IsProper (curveToBase K) ∧ IsNoetherian (curveScheme K) :=
  _root_.MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K h104
theorem curveScheme_isIntegral : IsIntegral (curveScheme K) :=
  (actual_good_characteristic_geometry K h104).1
theorem curveToBase_smooth_relativeDimension_one : SmoothOfRelativeDimension 1 (curveToBase K) :=
  (actual_good_characteristic_geometry K h104).2.1
end MazurTransfer.Order13GoodCharacteristicGeometry
namespace MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]
instance actualCurve_publicSmooth : Smooth (curveToBase K) := by
  letI : SmoothOfRelativeDimension 1 (curveToBase K) :=
    Order13GoodCharacteristicGeometry.curveToBase_smooth_relativeDimension_one K Fact.out
  exact SmoothOfRelativeDimension.smooth 1 _
instance actualCurve_publicNoetherian : IsNoetherian (curveScheme K) :=
  (Order13GoodCharacteristicGeometry.actual_good_characteristic_geometry K Fact.out).2.2.2
end MazurTransfer.Order13GoodCharacteristicCurveModel
end
end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: coefficient coordinates for the monic quadratic algebra.
Named downstream consumer: actual hyperelliptic overlap and chart sections.
-/

noncomputable section
namespace MazurTransfer.QuadraticCoordinates
open Polynomial Module
variable (R : Type*) [CommRing R] [Nontrivial R] (f : R)



















end MazurTransfer.QuadraticCoordinates


end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: actual function-field places and closed points from the
literal good-characteristic curve's checked geometry, with every geometry
instance explicit. Named downstream consumer: public effective degree-two
divisor counts. No supplied model or finite-set affine-open hypothesis is
used by this smaller place foundation.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]

instance actualCurve_isIntegral : IsIntegral (curveScheme K) := Order13GoodCharacteristicGeometry.curveScheme_isIntegral K Fact.out

instance actualCurve_smoothRelativeDimensionOne : SmoothOfRelativeDimension 1 (curveToBase K) :=
  Order13GoodCharacteristicGeometry.curveToBase_smooth_relativeDimension_one K Fact.out

instance actualCurve_isProper : IsProper (curveToBase K) :=
  (Order13GoodCharacteristicGeometry.actual_good_characteristic_geometry K Fact.out).2.2.1

instance actualCurve_isNoetherian : IsNoetherian (curveScheme K) :=
  (Order13GoodCharacteristicGeometry.actual_good_characteristic_geometry K Fact.out).2.2.2

instance actualCurve_isSmooth : Smooth (curveToBase K) :=
  SmoothOfRelativeDimension.smooth 1 _

abbrev actualCurveFunctionField : Type u := (curveScheme K).functionField

instance actualCurveFunctionFieldAlgebra : Algebra K (actualCurveFunctionField K) :=
  (baseToFunctionField (curveToBase K)).toAlgebra

def actualPlaceOfPoint (x : closedPoints (curveScheme K)) : Place K (actualCurveFunctionField K) :=
  Classical.choose (_root_.AlgebraicCurve.exists_place_range_stalk_eq
    (curveToBase K) x.1 (mem_closedPoints_iff.mp x.2))

theorem actualPlaceOfPoint_stalk_range (x : closedPoints (curveScheme K)) :
    (algebraMap ((curveScheme K).presheaf.stalk x.1) (actualCurveFunctionField K)).range =
      (actualPlaceOfPoint K x).toValuationSubring.toSubring :=
  Classical.choose_spec (_root_.AlgebraicCurve.exists_place_range_stalk_eq
    (curveToBase K) x.1 (mem_closedPoints_iff.mp x.2))



end MazurTransfer.Order13GoodCharacteristicCurveModel

end

end


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the literal order-13 curve's genuine place/cohomology and
Riemann–Roch infrastructure over every perfect field where 104 is nonzero.
Named downstream consumer: finite-field degree-two divisor classes and
the actual Picard cardinality calculation over F3 and F5.
Adapted from the previously checked owned characteristic-zero bridge by
using the actual good-characteristic CurveModel and its proved geometry.
Complete official Anthropic FLT mathematical APIs retain their source pin
6e837e75355538c7f80bab5b956861e86c4eacc2 and Apache-2.0 provenance.
-/

noncomputable section
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTorsion _root_.MazurTorsion.XOneThirteenAffineCurve _root_.MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]

instance actualFunctionFieldIsCurveOver : IsCurveOver K (actualCurveFunctionField K) :=
  AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    (curveToBase K) (RingEquiv.refl _) (fun _ => rfl)

end MazurTransfer.Order13GoodCharacteristicCurveModel

end

end



end GoodCharacteristicGeometryPublicProof
#print axioms GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualPlaceOfPoint


