-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldDiamondPicardEndomorphismsData
-- name    : MazurTransfer_Order13FieldDiamondPicardEndomorphismsData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T17:33:30.742225+00:00
-- url     : https://prove2.me/theorems/9ea1644e-b3d0-4dd9-a976-7bb7bc794059
-- title:
--   The actual arithmetic Picard diamond and descent endomorphisms over characteristic-zero fields
-- statement:
--   The complete original arithmetic degree-zero Picard group and diamond endomorphism rho, the literal endomorphisms pi=3+2rho and piConjugate=5-2rho, their power-action identities, sixth power, product expansions and commutation, over every characteristic-zero field. Ten original types, four data values and five original scalar algebra providers are compared. Named downstream consumer: geometric-field trace, cyclotomic norm and actual scheme norm transport.
-- source:
--   Complete original MazurTheorem Order13FieldDiamondPicardEndomorphisms, with original constructors and the published general-field exact diamond order. Official Anthropic FLT divisor-class action at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The function-field action on divisor classes uses the checked original
Anthropic FLT definitions at 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: actual arithmetic Picard endomorphisms (rho K), 3+2rho and
5-2rho from the literal diamond automorphism. Named downstream consumer:
the cyclotomic relation and nineteen-isogeny arithmetic descent. The norm
nineteen relation and rational rank zero are separate conclusions.
-/
import Definitions.Def_MazurTransfer_Order13FieldDiamondExactOrderData
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

noncomputable section
universe w
namespace MazurTransfer.Order13FieldDiamondPicardEndomorphisms
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13FieldDiamondFunctionFieldAutomorphism Order13FieldDiamondExactOrder
variable (K : Type w) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : CharZero (actualCurveFunctionField K) := Algebra.charZero_of_charZero K _

abbrev ActualPicard := Pic0 K (actualCurveFunctionField K)

def rho : AddMonoid.End (ActualPicard K) :=
  DistribSMul.toAddMonoidHom (ActualPicard K) (diamondAlgEquiv K)

theorem rho_apply (c : (ActualPicard K)) : (rho K) c = (diamondAlgEquiv K) • c := rfl

theorem rho_pow_apply (n : ℕ) (c : (ActualPicard K)) :
    ((rho K) ^ n) c = ((diamondAlgEquiv K) ^ n) • c := by
  induction n generalizing c with
  | zero => exact (one_smul _ c).symm
  | succ n ih =>
    rw [pow_succ, pow_succ]
    change ((rho K) ^ n) ((diamondAlgEquiv K) • c) = ((diamondAlgEquiv K) ^ n * (diamondAlgEquiv K)) • c
    rw [ih, mul_smul]

theorem rho_pow_six : (rho K) ^ 6 = 1 := by
  apply AddMonoidHom.ext
  intro c
  exact ((rho_pow_apply K) 6 c).trans
    ((congrArg (fun f => f • c) (diamondAlgEquiv_pow_six K)).trans (one_smul _ c))

def pi : AddMonoid.End (ActualPicard K) := 3 + 2 * (rho K)
def piConjugate : AddMonoid.End (ActualPicard K) := 5 - 2 * (rho K)

theorem pi_comp_piConjugate : (pi K) * (piConjugate K) = 15 + 4 * (rho K) - 4 * (rho K) ^ 2 := by
  apply AddMonoidHom.ext
  intro c
  change (3 : ℕ) • ((5 : ℕ) • c - (2 : ℕ) • (rho K) c) +
      (2 : ℕ) • (rho K) ((5 : ℕ) • c - (2 : ℕ) • (rho K) c) =
    (15 : ℕ) • c + (4 : ℕ) • (rho K) c - (4 : ℕ) • (rho K) ((rho K) c)
  rw [map_sub, map_nsmul, map_nsmul]
  abel

theorem piConjugate_comp_pi : (piConjugate K) * (pi K) = 15 + 4 * (rho K) - 4 * (rho K) ^ 2 := by
  apply AddMonoidHom.ext
  intro c
  change (5 : ℕ) • ((3 : ℕ) • c + (2 : ℕ) • (rho K) c) -
      (2 : ℕ) • (rho K) ((3 : ℕ) • c + (2 : ℕ) • (rho K) c) =
    (15 : ℕ) • c + (4 : ℕ) • (rho K) c - (4 : ℕ) • (rho K) ((rho K) c)
  rw [map_add, map_nsmul, map_nsmul]
  abel

theorem pi_commute : Commute (pi K) (piConjugate K) := by
  exact (pi_comp_piConjugate K).trans (piConjugate_comp_pi K).symm

end MazurTransfer.Order13FieldDiamondPicardEndomorphisms
#print axioms MazurTransfer.Order13FieldDiamondPicardEndomorphisms.rho_pow_six
#print axioms MazurTransfer.Order13FieldDiamondPicardEndomorphisms.pi_comp_piConjugate
#print axioms MazurTransfer.Order13FieldDiamondPicardEndomorphisms.pi_commute


