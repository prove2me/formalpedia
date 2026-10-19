-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldPicardDiamondTraceData
-- name    : MazurTransfer_Order13FieldPicardDiamondTraceData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T17:55:43.858776+00:00
-- url     : https://prove2.me/theorems/81eb5214-d4c2-42af-a646-5535ce14e2d8
-- title:
--   The literal diamond-square and diamond-cube arithmetic Picard traces over characteristic-zero fields
-- statement:
--   Over every characteristic-zero field K, the original literal diamond-square trace c+rho^2(c)+rho^4(c) and diamond-cube trace c+rho^3(c) vanish on the actual arithmetic degree-zero Picard group. The original order-three and order-two arguments and both complete trace proofs are retained. Four original types and all five original local scalar algebra providers are compared; dependency scalar providers were separately compared in their original constructor packages. Named downstream consumer: geometric-field Picard cyclotomic identity and actual scheme norm.
-- source:
--   Complete original MazurTheorem Order13FieldPicardDiamondTrace, with public actual rational fixed-field data and the accepted cyclic arithmetic Pic0 trace theorem. The curve-over-field certificate is the explicit projection of the accepted actual function-field invariants. Official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: Galois Picard traces for the actual diamond-square and
hyperelliptic diamond-cube fixed fields. Named downstream consumer: the
cyclotomic relation and norm nineteen of the actual Picard endomorphisms.
-/
import Theorems.Thm_MazurTransfer_RationalFixedFieldPicardTrace_cyclic_pic0_trace_eq_zero
import Definitions.Def_MazurTransfer_Order13FieldHyperellipticFixedFieldData
import Definitions.Def_MazurTransfer_Order13FieldOrderThreeFixedFieldData
import Definitions.Def_MazurTransfer_Order13FieldDiamondPicardEndomorphismsData
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants

noncomputable section
universe w
namespace MazurTransfer.Order13FieldPicardDiamondTrace
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13FieldConicFieldCubicExtension Order13FieldHyperellipticFixedField
open Order13FieldDiamondFunctionFieldAutomorphism Order13FieldDiamondExactOrder
open Order13FieldDiamondPicardEndomorphisms RationalFixedFieldPicardTrace
variable (K : Type w) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : CharZero (actualCurveFunctionField K) := Algebra.charZero_of_charZero K _
local instance (B : IntermediateField K (actualCurveFunctionField K)) : Algebra K B :=
  IntermediateField.algebra' B
local instance : Algebra K (conicField K) := IntermediateField.algebra' (conicField K)
local instance : Algebra K (xField K) := IntermediateField.algebra' (xField K)
local instance : Algebra K (RatFunc K) := RatFunc.instAlgebraOfPolynomial K K
local instance : IsCurveOver K (actualCurveFunctionField K) :=
  (MazurTransfer.order13_actual_function_field_invariants K Fact.out).1

theorem diamond_square_order : orderOf ((diamondAlgEquiv K) ^ 2) = 3 := by
  rw [orderOf_pow' (x := (diamondAlgEquiv K)) (n := 2) (by decide), (diamondAlgEquiv_order K)]
  norm_num

theorem diamond_cube_order : orderOf ((diamondAlgEquiv K) ^ 3) = 2 := by
  rw [orderOf_pow' (x := (diamondAlgEquiv K)) (n := 3) (by decide), (diamondAlgEquiv_order K)]
  norm_num

theorem order_three_trace_zero (c : (ActualPicard K)) :
    c + ((rho K) ^ 2) c + ((rho K) ^ 4) c = 0 := by
  let e : RatFunc K ≃ₐ[K] IntermediateField.fixedField
      (Subgroup.zpowers ((diamondAlgEquiv K) ^ 2)) :=
    (Order13FieldOrderThreeFixedField.rationalQuotientFieldEquiv K).trans
      (IntermediateField.equivOfEq
        (Order13FieldOrderThreeFixedField.actual_order_three_fixed_field K))
  have hfinite : IsOfFinOrder ((diamondAlgEquiv K) ^ 2) := by
    exact orderOf_pos_iff.mp (by rw [(diamond_square_order K)]; decide)
  have h := cyclic_pic0_trace_eq_zero ((diamondAlgEquiv K) ^ 2) hfinite e c
  rw [(diamond_square_order K)] at h
  simpa [Fin.sum_univ_succ, pow_succ, (rho_pow_apply K), (rho_apply K), mul_smul, add_assoc] using h

theorem hyperelliptic_trace_zero (c : (ActualPicard K)) : c + ((rho K) ^ 3) c = 0 := by
  let e : RatFunc K ≃ₐ[K] IntermediateField.fixedField
      (Subgroup.zpowers ((diamondAlgEquiv K) ^ 3)) :=
    (rationalInvolutionFieldEquiv K).trans
      (IntermediateField.equivOfEq (actual_hyperelliptic_fixed_field K))
  have hfinite : IsOfFinOrder ((diamondAlgEquiv K) ^ 3) := by
    exact orderOf_pos_iff.mp (by rw [(diamond_cube_order K)]; decide)
  have h := cyclic_pic0_trace_eq_zero ((diamondAlgEquiv K) ^ 3) hfinite e c
  rw [(diamond_cube_order K)] at h
  simpa [Fin.sum_univ_succ, pow_succ, (rho_pow_apply K), (rho_apply K), mul_smul] using h

end MazurTransfer.Order13FieldPicardDiamondTrace
#print axioms MazurTransfer.Order13FieldPicardDiamondTrace.order_three_trace_zero
#print axioms MazurTransfer.Order13FieldPicardDiamondTrace.hyperelliptic_trace_zero


