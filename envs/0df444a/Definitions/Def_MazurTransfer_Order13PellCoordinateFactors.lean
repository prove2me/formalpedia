-- Prove2me | Definitions.Def_MazurTransfer_Order13PellCoordinateFactors
-- name    : MazurTransfer_Order13PellCoordinateFactors
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:08:01.848997+00:00
-- url     : https://prove2.me/theorems/7ba11bf3-8ea6-45ea-8dde-63214a6bedfd
-- title:
--   The explicit Pell factors in the actual coordinate algebras
-- statement:
--   For the two literal coordinate algebras over a commutative ring $R$, the original ordinary factors $H(x)\pm yK(x)$ and reciprocal factors $H_\infty(z)\pm wK_\infty(z)$ satisfy $$P_+P_-=-4,\qquad P_{\infty,+}P_{\infty,-}=-4z^{38}.$$ If $2$ is a unit in $R$, both ordinary factors are units in the ordinary coordinate algebra. These exact coordinate elements supply the actual Pell function and its infinity divisor calculation.
-- source:
--   Original complete selected declarations and bodies from MazurTheorem, Apache-2.0, Vas and contributors. 7 complete original closed types and 4 data values are kernel-compared; native, strict and complete frontend checks pass with standard axioms only. Public imports alone replace the original project dependencies. Original polynomial coefficients and upstream attribution are retained. Design boundary and named downstream consumers are explicit in the checked source and original-source preparation manifest.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Polynomial coefficients and Pell identities adapted from MazurTheorem,
MazurTorsion/NumberTheory/XOneThirteenDescent.lean, user source pin
54d43d8dda8a6fcf069cc02a815f850d762c5c0c; source SHA-256
10a30be619946d1c2a3207bffb758840f80ff71dcbb0ee5c3dd0d068cc80961f.
Design boundary: the literal Pell polynomial certificate over arbitrary
commutative rings and its evaluation on the two actual coordinate charts.
Named downstream consumer: the actual degree-19 principal-divisor computation.
-/
/- Design boundary: the explicit Pell factors in the two actual coordinate
algebras, with their original product and ordinary-unit certificates.
Named downstream consumer: the actual Pell function and degree-19 principal divisor. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_MazurTransfer_Order13PellPolynomialCertificate
noncomputable section
universe u
namespace MazurTransfer.Order13PellChartCertificate
open Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
variable {R : Type u} [CommRing R]
def ordinaryPlus (R : Type u) [CommRing R] : CoordinateRing R :=
  pellH (xCoordinate R) + yCoordinate R * pellK (xCoordinate R)

def ordinaryMinus (R : Type u) [CommRing R] : CoordinateRing R :=
  pellH (xCoordinate R) - yCoordinate R * pellK (xCoordinate R)

def reciprocalPlus (R : Type u) [CommRing R] : ReciprocalRing R :=
  infinityPellH (zCoordinate R) + wCoordinate R * infinityPellK (zCoordinate R)

def reciprocalMinus (R : Type u) [CommRing R] : ReciprocalRing R :=
  infinityPellH (zCoordinate R) - wCoordinate R * infinityPellK (zCoordinate R)

theorem ordinary_product (R : Type u) [CommRing R] :
    ordinaryPlus R * ordinaryMinus R = -4 := by
  apply pell_factorization
  have hy := yCoordinate_sq R
  simpa only [sexticPolynomial, sextic, map_add, map_mul, map_pow,
    _root_.map_ofNat, _root_.map_one, aeval_X] using hy

theorem reciprocal_product (R : Type u) [CommRing R] :
    reciprocalPlus R * reciprocalMinus R = -4 * zCoordinate R ^ 38 := by
  apply infinity_pell_factorization
  have hw := wCoordinate_sq R
  simpa only [reciprocalPolynomial, infinitySextic, map_add, map_mul, map_pow,
    _root_.map_ofNat, _root_.map_one, aeval_X, add_comm, add_left_comm, add_assoc] using hw

theorem ordinary_factors_are_units (R : Type u) [CommRing R] (h2 : IsUnit (2 : R)) :
    IsUnit (ordinaryPlus R) ∧ IsUnit (ordinaryMinus R) := by
  have h4 : IsUnit (-4 : CoordinateRing R) := by
    have h := (h2.map (algebraMap R (CoordinateRing R))).pow 2
    have heq : (2 : CoordinateRing R) ^ 2 = 4 := by ring
    simpa only [map_ofNat, heq] using h.neg
  have h := h4
  rw [← ordinary_product] at h
  exact ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩
end MazurTransfer.Order13PellChartCertificate
#print axioms MazurTransfer.Order13PellChartCertificate.ordinary_factors_are_units


