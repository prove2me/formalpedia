-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldFunctionFieldGeneratorsData
-- name    : MazurTransfer_Order13FieldFunctionFieldGeneratorsData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T17:29:18.843814+00:00
-- url     : https://prove2.me/theorems/15d96a02-d4e1-4592-b459-6af7b116812d
-- title:
--   The literal ordinary coordinates generate the actual curve function field over characteristic-zero fields
-- statement:
--   Over every characteristic-zero field K, any intermediate field of the actual scheme function field containing the original x and y coordinate images is the whole field; equivalently their field adjoin is top. Both complete original theorem types and the two current/dependency scalar algebra providers are compared. Named downstream consumer: the literal cubic extension over the quotient conic parameter.
-- source:
--   Complete original MazurTheorem Order13FieldFunctionFieldGenerators proof using coordinate-ring induction and the fraction-ring representation of the actual scheme function field. Official Anthropic FLT curve interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal ordinary coordinates generate the actual
scheme function field over any characteristic-zero field as a field. Named downstream consumer: the
cyclic (cubic K) extension over the literal quotient-conic parameter.
-/
import Definitions.Def_MazurTransfer_Order13FieldOrdinaryPolynomialTranscendenceData

noncomputable section
universe w
namespace MazurTransfer.Order13FieldFunctionFieldGenerators
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13FieldOrdinaryPolynomialTranscendence
variable (K : Type w) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : CharZero (actualCurveFunctionField K) := Algebra.charZero_of_charZero K _

theorem intermediateField_eq_top (S : IntermediateField K (actualCurveFunctionField K))
    (hx : xImage K ∈ S) (hy : yImage K ∈ S) : S = ⊤ := by
  have hcoeff (p : Polynomial K) : (polynomialEmbedding K) p ∈ S := by
    change (polynomialAlgHom K) p ∈ S
    rw [(polynomialAlgHom_eq_aeval K)]
    exact (Algebra.adjoin_le (by simpa using hx) :
      Algebra.adjoin K {xImage K} ≤ S.toSubalgebra) (Polynomial.aeval_mem_adjoin_singleton K (xImage K) (p := p))
  have hcoordinate (a : CoordinateRing K) :
      algebraMap (CoordinateRing K) (actualCurveFunctionField K) a ∈ S := by
    induction a using AdjoinRoot.induction_on with
    | ih p =>
      induction p using Polynomial.induction_on with
      | C c => exact hcoeff c
      | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
      | monomial n c ih =>
        rw [pow_succ, ← mul_assoc, map_mul, map_mul]
        exact S.mul_mem ih hy
  apply top_unique
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (CoordinateRing K) z
  exact S.div_mem (hcoordinate a) (hcoordinate b)

theorem coordinates_generate :
    IntermediateField.adjoin K {xImage K, yImage K} = ⊤ := by
  apply (intermediateField_eq_top K)
  · exact IntermediateField.subset_adjoin K _ (by simp)
  · exact IntermediateField.subset_adjoin K _ (by simp)

end MazurTransfer.Order13FieldFunctionFieldGenerators
#print axioms MazurTransfer.Order13FieldFunctionFieldGenerators.coordinates_generate


