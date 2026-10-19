-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
-- name    : MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T16:50:27.790975+00:00
-- url     : https://prove2.me/theorems/eb597e00-5929-490f-b8f0-1e32875b97b4
-- title:
--   Original arithmetic diamond Picard endomorphisms and conjugate candidates
-- statement:
--   The original ActualPicard, rho, pi=3+2rho and piConjugate=5-2rho constructors are retained with their original power and composite-expansion certificates. Ten original types and four data values are checked. The sixth-power proof derives its certificate from the accepted public exact-order-six theorem; all theorem contracts and constructor values are unchanged. This does not assert the separate cyclotomic, norm-nineteen or rank-zero conclusions. Named downstream consumer: literal diamond trace and cyclotomic norm.
-- source:
--   Original complete MazurTheorem fixed-field/arithmetic Picard constructors and theorem contracts, Apache-2.0, Vas and contributors. Official Anthropic FLT divisor-class action at 6e837e75355538c7f80bab5b956861e86c4eacc2. Original full types and non-proof data values kernel-compared; the public exact-order certificate supplies the endomorphism sixth-power proof.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The function-field action on divisor classes uses the checked original
Anthropic FLT definitions at 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: actual arithmetic Picard endomorphisms rho, 3+2rho and
5-2rho from the literal diamond automorphism. Named downstream consumer:
the cyclotomic relation and nineteen-isogeny arithmetic descent. The norm
nineteen relation and rational rank zero are separate conclusions.
-/
import Theorems.Thm_MazurTransfer_Order13ActualDiamondExactOrder_diamondAlgEquiv_order
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

noncomputable section
namespace MazurTransfer.Order13ActualDiamondPicardEndomorphisms
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualDiamondFunctionFieldAutomorphism Order13ActualDiamondExactOrder
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

abbrev ActualPicard := Pic0 ℚ (actualCurveFunctionField ℚ)

def rho : AddMonoid.End ActualPicard :=
  DistribSMul.toAddMonoidHom ActualPicard diamondAlgEquiv

theorem rho_apply (c : ActualPicard) : rho c = diamondAlgEquiv • c := rfl

theorem rho_pow_apply (n : ℕ) (c : ActualPicard) :
    (rho ^ n) c = (diamondAlgEquiv ^ n) • c := by
  induction n generalizing c with
  | zero => exact (one_smul _ c).symm
  | succ n ih =>
    rw [pow_succ, pow_succ]
    change (rho ^ n) (diamondAlgEquiv • c) = (diamondAlgEquiv ^ n * diamondAlgEquiv) • c
    rw [ih, mul_smul]

theorem rho_pow_six : rho ^ 6 = 1 := by
  apply AddMonoidHom.ext
  intro c
  exact (rho_pow_apply 6 c).trans
    ((congrArg (fun f => f • c) (by rw [← diamondAlgEquiv_order]; exact pow_orderOf_eq_one diamondAlgEquiv)).trans (one_smul _ c))

def pi : AddMonoid.End ActualPicard := 3 + 2 * rho
def piConjugate : AddMonoid.End ActualPicard := 5 - 2 * rho

theorem pi_comp_piConjugate : pi * piConjugate = 15 + 4 * rho - 4 * rho ^ 2 := by
  apply AddMonoidHom.ext
  intro c
  change (3 : ℕ) • ((5 : ℕ) • c - (2 : ℕ) • rho c) +
      (2 : ℕ) • rho ((5 : ℕ) • c - (2 : ℕ) • rho c) =
    (15 : ℕ) • c + (4 : ℕ) • rho c - (4 : ℕ) • rho (rho c)
  rw [map_sub, map_nsmul, map_nsmul]
  abel

theorem piConjugate_comp_pi : piConjugate * pi = 15 + 4 * rho - 4 * rho ^ 2 := by
  apply AddMonoidHom.ext
  intro c
  change (5 : ℕ) • ((3 : ℕ) • c + (2 : ℕ) • rho c) -
      (2 : ℕ) • rho ((3 : ℕ) • c + (2 : ℕ) • rho c) =
    (15 : ℕ) • c + (4 : ℕ) • rho c - (4 : ℕ) • rho (rho c)
  rw [map_add, map_nsmul, map_nsmul]
  abel

theorem pi_commute : Commute pi piConjugate := by
  exact pi_comp_piConjugate.trans piConjugate_comp_pi.symm

end MazurTransfer.Order13ActualDiamondPicardEndomorphisms
#print axioms MazurTransfer.Order13ActualDiamondPicardEndomorphisms.rho_pow_six
#print axioms MazurTransfer.Order13ActualDiamondPicardEndomorphisms.pi_comp_piConjugate
#print axioms MazurTransfer.Order13ActualDiamondPicardEndomorphisms.pi_commute


