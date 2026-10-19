-- Prove2me | Definitions.Def_MazurTransfer_Order13PellPolynomialCertificate
-- name    : MazurTransfer_Order13PellPolynomialCertificate
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:02:37.809854+00:00
-- url     : https://prove2.me/theorems/221566b6-66f7-43ae-a9d4-a2f052205529
-- title:
--   The original universal Pell polynomial certificate
-- statement:
--   Over any commutative ring, the original explicit polynomials satisfy $$H(x)^2-s(x)K(x)^2=-4,\qquad H_\infty(z)^2-s_\infty(z)K_\infty(z)^2=-4z^{38}.$$ The original factorizations into the two conjugate linear expressions are retained. This supplies the polynomial input for the actual Pell functions and their degree-nineteen principal divisor.
-- source:
--   Original complete selected declarations and bodies from MazurTheorem, Apache-2.0, Vas and contributors. 9 complete original closed types and 5 data values are kernel-compared; native, strict and complete frontend checks pass with standard axioms only. Public imports alone replace the original project dependencies. Original polynomial coefficients and upstream attribution are retained. Design boundary and named downstream consumers are explicit in the checked source and original-source preparation manifest.

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
/- Design boundary: the original universal Pell polynomials and their exact
ring certificates, before evaluation in the actual coordinate rings.
Named downstream consumer: actual Pell functions and the degree-19 principal divisor. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13LiteralSextic
noncomputable section
universe u
namespace MazurTransfer.Order13PellChartCertificate
variable {R : Type u} [CommRing R]
def pellH (x : R) : R :=
  x ^ 19 + 3 * x ^ 18 + 2 * x ^ 17 + 5 * x ^ 16 +
    22 * x ^ 15 + 22 * x ^ 14 + 10 * x ^ 13 +
    54 * x ^ 12 + 78 * x ^ 11 + 20 * x ^ 10 +
    51 * x ^ 9 + 113 * x ^ 8 + 36 * x ^ 7 +
    13 * x ^ 6 + 66 * x ^ 5 + 26 * x ^ 4 -
    2 * x ^ 3 + 12 * x ^ 2 + 4 * x

def pellK (x : R) : R :=
  x ^ 16 + 2 * x ^ 15 + 4 * x ^ 13 + 14 * x ^ 12 +
    4 * x ^ 11 + 2 * x ^ 10 + 32 * x ^ 9 +
    18 * x ^ 8 - 8 * x ^ 7 + 29 * x ^ 6 +
    24 * x ^ 5 - 10 * x ^ 4 + 10 * x ^ 3 +
    10 * x ^ 2 - 4 * x + 2

def infinitySextic (z : R) : R :=
  1 + 2 * z + z ^ 2 + 2 * z ^ 3 +
    6 * z ^ 4 + 4 * z ^ 5 + z ^ 6

def infinityPellH (z : R) : R :=
  1 + 3 * z + 2 * z ^ 2 + 5 * z ^ 3 +
    22 * z ^ 4 + 22 * z ^ 5 + 10 * z ^ 6 +
    54 * z ^ 7 + 78 * z ^ 8 + 20 * z ^ 9 +
    51 * z ^ 10 + 113 * z ^ 11 + 36 * z ^ 12 +
    13 * z ^ 13 + 66 * z ^ 14 + 26 * z ^ 15 -
    2 * z ^ 16 + 12 * z ^ 17 + 4 * z ^ 18

def infinityPellK (z : R) : R :=
  1 + 2 * z + 4 * z ^ 3 + 14 * z ^ 4 +
    4 * z ^ 5 + 2 * z ^ 6 + 32 * z ^ 7 +
    18 * z ^ 8 - 8 * z ^ 9 + 29 * z ^ 10 +
    24 * z ^ 11 - 10 * z ^ 12 + 10 * z ^ 13 +
    10 * z ^ 14 - 4 * z ^ 15 + 2 * z ^ 16

theorem pell_identity (x : R) : pellH x ^ 2 - sextic x * pellK x ^ 2 = -4 := by
  simp only [pellH, pellK, sextic]
  ring

theorem infinity_pell_identity (z : R) :
    infinityPellH z ^ 2 - infinitySextic z * infinityPellK z ^ 2 = -4 * z ^ 38 := by
  simp only [infinityPellH, infinityPellK, infinitySextic]
  ring

theorem pell_factorization (x y : R) (hy : y ^ 2 = sextic x) :
    (pellH x + y * pellK x) * (pellH x - y * pellK x) = -4 := by
  calc
    _ = pellH x ^ 2 - y ^ 2 * pellK x ^ 2 := by ring
    _ = -4 := by rw [hy]; exact pell_identity x

theorem infinity_pell_factorization (z w : R) (hw : w ^ 2 = infinitySextic z) :
    (infinityPellH z + w * infinityPellK z) *
      (infinityPellH z - w * infinityPellK z) = -4 * z ^ 38 := by
  calc
    _ = infinityPellH z ^ 2 - w ^ 2 * infinityPellK z ^ 2 := by ring
    _ = -4 * z ^ 38 := by rw [hw]; exact infinity_pell_identity z
end MazurTransfer.Order13PellChartCertificate
#print axioms MazurTransfer.Order13PellChartCertificate.pell_identity
#print axioms MazurTransfer.Order13PellChartCertificate.infinity_pell_identity


