-- Prove2me | Definitions.Def_MohP3_Defs
-- name    : MohP3_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:44:13.68177+00:00
-- url     : https://prove2.me/theorems/a6db5d7c-5cfd-4bc2-bce2-06d9536e2d14
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MvPolynomial
namespace MohP3
abbrev R := MvPolynomial (Fin 3) ℚ
def x : R := X 0
def y : R := X 1
def z : R := X 2
def f1 : R :=
  x^4 - x^2*y^4*z^3 - 2*x*y^6*z^2 - 4*x*y*z - 3*y^3*z^5 + 3*y^3
def f2 : R :=
  x^3*y - x*y^5*z^3 - 3*x*z^2 - 2*y^7*z^2 + 2*y^2*z
def f3 : R :=
  2*x^3*z - 3*x^2*y^2 - 2*x*y^4*z^4 - y^6*z^3 + y*z^2
def f4 : R :=
  x^2*y*z - 2*x*y^3 - y^5*z^4 + z^3
def ell : R :=
  64*x^4*y*z^2 - 40*x^3*y^3*z + 72*x*y^2*z^3 - 81*y^4*z^2
def kappa : R :=
  -40*x^3*y^2*z^2 + 25*x^2*y^4*z + 36*y^3*z^3
def H1 : R := 81*f4 - 24*x*f1 + ell*f3
def H2 : R := -12*y*f1 + 27*x*f2 + kappa*f3
def P : Ideal R := Ideal.span ({f1, f2, f3, f4} : Set R)
def Q : Ideal R := Ideal.span ({H1, H2} : Set R)
abbrev T := Polynomial ℚ
def rho : R →+* T :=
  eval₂Hom Polynomial.C ![
    Polynomial.X^6 + Polynomial.X^31,
    Polynomial.X^8,
    Polynomial.X^10]
end MohP3


