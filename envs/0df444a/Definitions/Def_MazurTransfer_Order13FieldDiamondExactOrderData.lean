-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldDiamondExactOrderData
-- name    : MazurTransfer_Order13FieldDiamondExactOrderData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T17:23:59.379041+00:00
-- url     : https://prove2.me/theorems/b4d017a2-7aff-4e99-9273-44b4faa3f3fd
-- title:
--   The actual diamond field automorphism has exact order six over every characteristic-zero field
-- statement:
--   The complete original actual diamond exact-order package over every characteristic-zero base field: nonzero ordinate, nonfixed abscissa, sixth power one, nontrivial cube and square, and exact order six. Six original theorem types and four original scalar algebra providers are compared. Named downstream consumer: the actual general-field rational fixed fields and geometric Picard cyclotomic norm.
-- source:
--   Complete original MazurTheorem Order13FieldDiamondExactOrder with the published general-field diamond algebra automorphism. Official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual function-field automorphism has exact order
six; its cube is a nontrivial hyperelliptic involution. Named downstream
consumer: the actual Picard action used by the nineteen-isogeny descent.
-/
import Definitions.Def_MazurTransfer_Order13FieldDiamondFunctionFieldAutomorphismData

noncomputable section
universe u
namespace MazurTransfer.Order13FieldDiamondExactOrder
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
open Order13FieldOrdinaryPolynomialTranscendence Order13FieldDiamondFunctionFieldMap
open Order13FieldDiamondFunctionFieldAutomorphism Order13DiamondSexticSymmetry
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : CharZero (actualCurveFunctionField K) := Algebra.charZero_of_charZero K _

theorem yImage_ne_zero : yImage K ≠ 0 := by
  have Hp : sexticPolynomial K ≠ 0 := by
    intro H
    have H6 := congrArg (fun p : Polynomial K => p.coeff 6) H
    norm_num [sexticPolynomial, Polynomial.coeff_X, Polynomial.coeff_one] at H6
  have He : aeval (xImage K) (sexticPolynomial K) =
      Order13PellChartCertificate.sextic (xImage K) := by
    simp only [sexticPolynomial, Order13PellChartCertificate.sextic,
      map_add, map_mul, map_pow, map_ofNat, map_one, aeval_X]
  have Hne := (map_ne_zero_iff (aeval (xImage K))
    (transcendental_iff_injective.mp (xImage_transcendental K))).mpr Hp
  rw [He, ← (yImage_sq K)] at Hne
  intro H
  apply Hne
  simp only [H, zero_pow (by decide : 2 ≠ 0)]

theorem diamondX_ne_xImage : diamondX (xImage K) ≠ xImage K := by
  intro H
  have Hden := (xImage_add_one_ne_zero K)
  have Hmul : -1 = xImage K * (xImage K + 1) := (div_eq_iff Hden).mp H
  have He : xImage K ^ 2 + xImage K + 1 = 0 := by linear_combination -Hmul
  apply (xImage_transcendental K)
  refine ⟨X ^ 2 + X + 1, ?_, ?_⟩
  · intro H
    have H2 := congrArg (fun p : Polynomial K => p.coeff 2) H
    norm_num [Polynomial.coeff_X, Polynomial.coeff_one] at H2
  · simpa only [map_add, map_pow, map_one, aeval_X] using He

theorem diamondAlgEquiv_pow_six : (diamondAlgEquiv K) ^ 6 = 1 := by
  apply AlgEquiv.ext
  intro b
  exact RingHom.congr_fun (diamondThird_square K) b

theorem diamondAlgEquiv_cube_ne_one : (diamondAlgEquiv K) ^ 3 ≠ 1 := by
  intro H
  have Hy := congrArg (fun f : actualCurveFunctionField K ≃ₐ[K] actualCurveFunctionField K =>
    f (yImage K)) H
  change (diamondThird K) (yImage K) = yImage K at Hy
  rw [(diamondThird_y K)] at Hy
  have Hz : (2 : actualCurveFunctionField K) * yImage K = 0 := by linear_combination -Hy
  rcases mul_eq_zero.mp Hz with H2 | Hy
  · norm_num at H2
  · exact (yImage_ne_zero K) Hy

theorem diamondAlgEquiv_square_ne_one : (diamondAlgEquiv K) ^ 2 ≠ 1 := by
  intro H
  have Hx := congrArg (fun f : actualCurveFunctionField K ≃ₐ[K] actualCurveFunctionField K =>
    f (xImage K)) H
  change (diamondSecond K) (xImage K) = xImage K at Hx
  have H3 := (diamondThird_x K)
  change (diamondFieldMap K) ((diamondSecond K) (xImage K)) = xImage K at H3
  rw [Hx, (diamondFieldMap_x K)] at H3
  exact (diamondX_ne_xImage K) H3

theorem diamondAlgEquiv_order : orderOf (diamondAlgEquiv K) = 6 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) (diamondAlgEquiv_pow_six K)
  intro p hp hd
  have Hp : p = 2 ∨ p = 3 := by
    have Hd : p ∣ 2 * 3 := hd
    rcases hp.dvd_mul.mp Hd with H2 | H3
    · exact Or.inl ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp H2 |>.resolve_left hp.ne_one)
    · exact Or.inr ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp H3 |>.resolve_left hp.ne_one)
  rcases Hp with rfl | rfl
  · exact (diamondAlgEquiv_cube_ne_one K)
  · exact (diamondAlgEquiv_square_ne_one K)

end MazurTransfer.Order13FieldDiamondExactOrder
#print axioms MazurTransfer.Order13FieldDiamondExactOrder.yImage_ne_zero
#print axioms MazurTransfer.Order13FieldDiamondExactOrder.diamondAlgEquiv_pow_six
#print axioms MazurTransfer.Order13FieldDiamondExactOrder.diamondAlgEquiv_order


