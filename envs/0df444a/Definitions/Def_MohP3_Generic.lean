-- Prove2me | Definitions.Def_MohP3_Generic
-- name    : MohP3_Generic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:46:43.75182+00:00
-- url     : https://prove2.me/theorems/f408d2fb-d8f1-47ed-8263-6545700d2014
-- title:
--   Generic
-- statement:
--   Definitions and structural lemmas for Generic, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace MohP3.Gen
variable {A : Type*} [CommRing A]
def f1 (x y z : A) : A :=
  x^4 - x^2*y^4*z^3 - 2*x*y^6*z^2 - 4*x*y*z - 3*y^3*z^5 + 3*y^3
def f2 (x y z : A) : A :=
  x^3*y - x*y^5*z^3 - 3*x*z^2 - 2*y^7*z^2 + 2*y^2*z
def f3 (x y z : A) : A :=
  2*x^3*z - 3*x^2*y^2 - 2*x*y^4*z^4 - y^6*z^3 + y*z^2
def f4 (x y z : A) : A :=
  x^2*y*z - 2*x*y^3 - y^5*z^4 + z^3
def ell (x y z : A) : A :=
  64*x^4*y*z^2 - 40*x^3*y^3*z + 72*x*y^2*z^3 - 81*y^4*z^2
def kappa (x y z : A) : A :=
  -40*x^3*y^2*z^2 + 25*x^2*y^4*z + 36*y^3*z^3
def H1 (x y z : A) : A := 81*f4 x y z - 24*x*f1 x y z + ell x y z*f3 x y z
def H2 (x y z : A) : A := -12*y*f1 x y z + 27*x*f2 x y z + kappa x y z*f3 x y z
def P (x y z : A) : Ideal A := Ideal.span ({f1 x y z, f2 x y z, f3 x y z, f4 x y z} : Set A)
def Q (x y z : A) : Ideal A := Ideal.span ({H1 x y z, H2 x y z} : Set A)
variable (x y z : A)
variable [Algebra ℚ A]
end MohP3.Gen


