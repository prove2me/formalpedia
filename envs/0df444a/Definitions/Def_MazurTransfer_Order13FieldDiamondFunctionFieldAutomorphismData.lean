-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldDiamondFunctionFieldAutomorphismData
-- name    : MazurTransfer_Order13FieldDiamondFunctionFieldAutomorphismData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T17:20:37.245875+00:00
-- url     : https://prove2.me/theorems/afde9556-85cd-4d93-b8ab-976bb0435c13
-- title:
--   The literal diamond is a base-field algebra automorphism over characteristic-zero fields
-- statement:
--   The original second and third diamond iterates, fifth-iterate inverse, function-field ring equivalence and base-field algebra equivalence for the actual order-thirteen scheme over every characteristic-zero field, together with all original coordinate, inverse and coefficient-preservation contracts. Fourteen full original types and five constructor values are compared, and three original current/dependency scalar algebra providers are compared separately. Named downstream consumer: exact field order, rational fixed fields and geometric Picard diamond action.
-- source:
--   Complete original MazurTheorem Order13FieldDiamondFunctionFieldAutomorphism, using the published general-field coordinate map and the published original generic iterate identities. Official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a genuine base-field algebra automorphism of the literal order-13
function field over every characteristic-zero field, whose cube fixes x and negates y. Named downstream consumer:
the induced Picard action and the nineteen-isogeny rank-zero descent.
-/
import Definitions.Def_MazurTransfer_Order13FieldDiamondFunctionFieldMapData
import Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism

noncomputable section
universe u
namespace MazurTransfer.Order13FieldDiamondFunctionFieldAutomorphism
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
open Order13FieldOrdinaryPolynomialTranscendence Order13FieldDiamondFunctionFieldMap
open Order13DiamondSexticSymmetry Order13DiamondSexticIterates
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

theorem fieldMap_ext_xy (f g : actualCurveFunctionField K →+* actualCurveFunctionField K)
    (hc : ∀ r : K, f (algebraMap K (actualCurveFunctionField K) r) =
      g (algebraMap K (actualCurveFunctionField K) r))
    (hx : f (xImage K) = g (xImage K)) (hy : f (yImage K) = g (yImage K)) : f = g := by
  apply IsFractionRing.ringHom_ext (A := CoordinateRing K)
  have H : f.comp (algebraMap (CoordinateRing K) (actualCurveFunctionField K)) =
      g.comp (algebraMap (CoordinateRing K) (actualCurveFunctionField K)) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext'
      · apply RingHom.ext
        intro r
        change f (algebraMap (CoordinateRing K) (actualCurveFunctionField K)
          (algebraMap K (CoordinateRing K) r)) = g (algebraMap (CoordinateRing K) (actualCurveFunctionField K)
          (algebraMap K (CoordinateRing K) r))
        rw [ordinaryEmbedding_algebraMap K]
        exact hc r
      · exact hx
    · exact hy
  exact fun b => RingHom.congr_fun H b

def diamondSecond : actualCurveFunctionField K →+* actualCurveFunctionField K :=
  (diamondFieldMap K).comp (diamondFieldMap K)
def diamondThird : actualCurveFunctionField K →+* actualCurveFunctionField K :=
  (diamondFieldMap K).comp (diamondSecond K)

theorem map_diamondX (f : actualCurveFunctionField K →+* actualCurveFunctionField K)
    (x : actualCurveFunctionField K) : f (diamondX x) = diamondX (f x) := by
  simp only [diamondX, map_div₀, map_neg, map_one, map_add]

theorem map_diamondY (f : actualCurveFunctionField K →+* actualCurveFunctionField K)
    (x y : actualCurveFunctionField K) : f (diamondY x y) = diamondY (f x) (f y) := by
  simp only [diamondY, map_div₀, map_pow, map_add, map_one]

theorem xImage_ne_zero : xImage K ≠ 0 := by
  intro H
  apply (xImage_transcendental K)
  rw [H]
  exact isIntegral_zero.isAlgebraic

theorem diamondThird_x : (diamondThird K) (xImage K) = xImage K := by
  simp only [diamondThird, diamondSecond, RingHom.comp_apply, (diamondFieldMap_x K), (map_diamondX K)]
  exact diamondX_cube (xImage K) (xImage_ne_zero K) (xImage_add_one_ne_zero K)

theorem diamondThird_y : (diamondThird K) (yImage K) = -yImage K := by
  simp only [diamondThird, diamondSecond, RingHom.comp_apply, (diamondFieldMap_y K), (map_diamondY K),
    (diamondFieldMap_x K), (map_diamondX K)]
  exact diamondY_cube (xImage K) (yImage K) (xImage_ne_zero K) (xImage_add_one_ne_zero K)

theorem diamondThird_square : (diamondThird K).comp (diamondThird K) = RingHom.id _ := by
  apply (fieldMap_ext_xy K)
  · intro r
    simp only [diamondThird, diamondSecond, RingHom.comp_apply, diamondFieldMap_algebraMap, RingHom.id_apply]
  · simp only [RingHom.comp_apply, (diamondThird_x K), RingHom.id_apply]
  · simp only [RingHom.comp_apply, (diamondThird_y K), map_neg, neg_neg, RingHom.id_apply]

def diamondInverse : actualCurveFunctionField K →+* actualCurveFunctionField K :=
  (diamondSecond K).comp (diamondThird K)

theorem diamond_inverse_left : (diamondInverse K).comp (diamondFieldMap K) = RingHom.id _ := by
  change (diamondFieldMap K).comp ((diamondFieldMap K).comp
    ((diamondFieldMap K).comp ((diamondFieldMap K).comp ((diamondFieldMap K).comp (diamondFieldMap K))))) = _
  exact (diamondThird_square K)

theorem diamond_inverse_right : (diamondFieldMap K).comp (diamondInverse K) = RingHom.id _ := by
  change (diamondFieldMap K).comp ((diamondFieldMap K).comp
    ((diamondFieldMap K).comp ((diamondFieldMap K).comp ((diamondFieldMap K).comp (diamondFieldMap K))))) = _
  exact (diamondThird_square K)

def diamondRingEquiv : actualCurveFunctionField K ≃+* actualCurveFunctionField K where
  __ := (diamondFieldMap K)
  invFun := (diamondInverse K)
  left_inv b := RingHom.congr_fun (diamond_inverse_left K) b
  right_inv b := RingHom.congr_fun (diamond_inverse_right K) b

def diamondAlgEquiv : actualCurveFunctionField K ≃ₐ[K] actualCurveFunctionField K :=
  AlgEquiv.ofRingEquiv (f := diamondRingEquiv K) (diamondFieldMap_algebraMap K)

end MazurTransfer.Order13FieldDiamondFunctionFieldAutomorphism
#print axioms MazurTransfer.Order13FieldDiamondFunctionFieldAutomorphism.fieldMap_ext_xy
#print axioms MazurTransfer.Order13FieldDiamondFunctionFieldAutomorphism.diamondThird_square
#print axioms MazurTransfer.Order13FieldDiamondFunctionFieldAutomorphism.diamondAlgEquiv


