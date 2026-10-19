-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualDiamondTraceArithmeticData
-- name    : MazurTransfer_Order13ActualDiamondTraceArithmeticData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T17:36:30.180372+00:00
-- url     : https://prove2.me/theorems/a6183355-2f35-4799-a0fd-a449b37631bc
-- title:
--   Paired original literal diamond-square and diamond-cube arithmetic Picard traces
-- statement:
--   Both original literal diamond arithmetic Picard trace identities, already separately Proved, with the original order-three and order-two proofs, exported under the original common namespace and one local instance context. Four original full theorem types and five original scalar algebra providers are compared. Named downstream consumer: the original arithmetic Picard cyclotomic and norm calculations. This packages the already accepted trace mathematics.
-- source:
--   Complete original MazurTheorem Order13ActualPicardDiamondTrace, retaining all four proofs. Uses public actual fixed-field and endomorphism definitions and the accepted generic cyclic Pic0 trace theorem. Official Anthropic FLT arithmetic Pic0 interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: Galois Picard traces for the actual diamond-square and
hyperelliptic diamond-cube fixed fields. Named downstream consumer: the
cyclotomic relation and norm nineteen of the actual Picard endomorphisms.
-/
import Definitions.Def_MazurTransfer_Order13ActualHyperellipticFixedFieldData
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Theorems.Thm_MazurTransfer_RationalFixedFieldPicardTrace_cyclic_pic0_trace_eq_zero

noncomputable section
namespace MazurTransfer.Order13ActualPicardDiamondTrace
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualConicFieldCubicExtension Order13ActualHyperellipticFixedField
open Order13ActualDiamondFunctionFieldAutomorphism Order13ActualDiamondExactOrder
open Order13ActualDiamondPicardEndomorphisms RationalFixedFieldPicardTrace
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
local instance (B : IntermediateField ℚ (actualCurveFunctionField ℚ)) : Algebra ℚ B :=
  IntermediateField.algebra' B
local instance : Algebra ℚ conicField := IntermediateField.algebra' conicField
local instance : Algebra ℚ xField := IntermediateField.algebra' xField
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
local instance : IsCurveOver ℚ (actualCurveFunctionField ℚ) :=
  (MazurTransfer.order13_actual_function_field_invariants ℚ Fact.out).1

theorem diamond_square_order : orderOf (diamondAlgEquiv ^ 2) = 3 := by
  rw [orderOf_pow' (x := diamondAlgEquiv) (n := 2) (by decide), diamondAlgEquiv_order]
  norm_num

theorem diamond_cube_order : orderOf (diamondAlgEquiv ^ 3) = 2 := by
  rw [orderOf_pow' (x := diamondAlgEquiv) (n := 3) (by decide), diamondAlgEquiv_order]
  norm_num

theorem order_three_trace_zero (c : ActualPicard) :
    c + (rho ^ 2) c + (rho ^ 4) c = 0 := by
  let e : RatFunc ℚ ≃ₐ[ℚ] IntermediateField.fixedField
      (Subgroup.zpowers (diamondAlgEquiv ^ 2)) :=
    Order13ActualOrderThreeFixedField.rationalQuotientFieldEquiv.trans
      (IntermediateField.equivOfEq
        Order13ActualOrderThreeFixedField.actual_order_three_fixed_field)
  have hfinite : IsOfFinOrder (diamondAlgEquiv ^ 2) := by
    exact orderOf_pos_iff.mp (by rw [diamond_square_order]; decide)
  have h := cyclic_pic0_trace_eq_zero (diamondAlgEquiv ^ 2) hfinite e c
  rw [diamond_square_order] at h
  simpa [Fin.sum_univ_succ, pow_succ, rho_pow_apply, rho_apply, mul_smul, add_assoc] using h

theorem hyperelliptic_trace_zero (c : ActualPicard) : c + (rho ^ 3) c = 0 := by
  let e : RatFunc ℚ ≃ₐ[ℚ] IntermediateField.fixedField
      (Subgroup.zpowers (diamondAlgEquiv ^ 3)) :=
    rationalInvolutionFieldEquiv.trans
      (IntermediateField.equivOfEq actual_hyperelliptic_fixed_field)
  have hfinite : IsOfFinOrder (diamondAlgEquiv ^ 3) := by
    exact orderOf_pos_iff.mp (by rw [diamond_cube_order]; decide)
  have h := cyclic_pic0_trace_eq_zero (diamondAlgEquiv ^ 3) hfinite e c
  rw [diamond_cube_order] at h
  simpa [Fin.sum_univ_succ, pow_succ, rho_pow_apply, rho_apply, mul_smul] using h

end MazurTransfer.Order13ActualPicardDiamondTrace
#print axioms MazurTransfer.Order13ActualPicardDiamondTrace.order_three_trace_zero
#print axioms MazurTransfer.Order13ActualPicardDiamondTrace.hyperelliptic_trace_zero


