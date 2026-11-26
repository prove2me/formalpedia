-- Prove2me | Definitions.Def_MohP3_Closure
-- name    : MohP3_Closure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:52:29.905+00:00
-- url     : https://prove2.me/theorems/217c36ff-8c81-4dcb-9152-9e3169f1c2bf
-- title:
--   Closure
-- statement:
--   Definitions and structural lemmas for Closure, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean

module
public import Definitions.Def_MohP3_Certificate
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MvPolynomial
namespace MohP3
def iota : Polynomial ℚ →+* R := Polynomial.eval₂RingHom MvPolynomial.C y
def hh : Fin 8 → R :=
  ![1, x, z, x^2, x*z - y^2, x^3 - y*z, z^2 - y*x^2, x^2*z - y^2*x - y^9]
def QX : Fin 8 → Fin 8 → Polynomial ℚ :=
![
  ![0, (18 : Polynomial ℚ), 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, (18 : Polynomial ℚ), 0, 0, 0, 0],
  ![18*Polynomial.X^2, 0, 0, 0, (18 : Polynomial ℚ), 0, 0, 0],
  ![0, 0, 18*Polynomial.X^1, 0, 0, (18 : Polynomial ℚ), 0, 0],
  ![18*Polynomial.X^9, 0, 0, 0, 0, 0, 0, (18 : Polynomial ℚ)],
  ![0, 12*Polynomial.X^21, 108*Polynomial.X^8, -54*Polynomial.X^14, 54*Polynomial.X^1, 24*Polynomial.X^7, -42*Polynomial.X^13, -12*Polynomial.X^19],
  ![0, 3*Polynomial.X^15, 0, -18*Polynomial.X^8, 0, -12*Polynomial.X^1, -15*Polynomial.X^7, -3*Polynomial.X^13],
  ![0, 9*Polynomial.X^9, 0, 0, 0, 0, -9*Polynomial.X^1, -9*Polynomial.X^7]]
def QZ : Fin 8 → Fin 8 → Polynomial ℚ :=
![
  ![0, 0, (18 : Polynomial ℚ), 0, 0, 0, 0, 0],
  ![18*Polynomial.X^2, 0, 0, 0, (18 : Polynomial ℚ), 0, 0, 0],
  ![0, 0, 0, 18*Polynomial.X^1, 0, 0, (18 : Polynomial ℚ), 0],
  ![18*Polynomial.X^9, 18*Polynomial.X^2, 0, 0, 0, 0, 0, (18 : Polynomial ℚ)],
  ![0, 3*Polynomial.X^15, 0, -18*Polynomial.X^8, 0, 6*Polynomial.X^1, -15*Polynomial.X^7, -3*Polynomial.X^13],
  ![0, 27*Polynomial.X^9, 0, 0, 0, 0, -27*Polynomial.X^1, -9*Polynomial.X^7],
  ![-18*Polynomial.X^10, 0, 0, 0, 0, 0, 0, -36*Polynomial.X^1],
  ![0, 0, 0, 0, 18*Polynomial.X^2, 0, 0, 0]]
end MohP3


