-- Prove2me | Definitions.Def_MohP3_HilbertBurch
-- name    : MohP3_HilbertBurch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:09:42.063831+00:00
-- url     : https://prove2.me/theorems/0fdb7ab8-4005-4845-9e70-f83ce4182a21
-- title:
--   Hilbert Burch
-- statement:
--   Definitions and structural lemmas for Hilbert Burch, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace MohP3.HilbertBurch
open Matrix
def maximalMinor {A : Type*} [CommRing A] (B : Matrix (Fin 4) (Fin 3) A) (i : Fin 4) : A :=
  (B.submatrix i.succAbove id).det
def phi {A : Type*} [CommRing A] (x y z : A) : Matrix (Fin 4) (Fin 3) A :=
  !![0,2*x*y,-2*z*(2*x*y^3*z^2+y^5*z-1);
     z,-2*x^2,y*(4*x^2*y*z^3+2*x*y^3*z^2-3);
     -2*y,-3*z,-x+6*y^2*z^4;
     3*x,3*y,0]
section General
variable {S : Type*} [CommRing S]
def rowMap (f : Fin 4 → S) : (Fin 4 → S) →ₗ[S] S where
  toFun a := a ⬝ᵥ f
  map_add' a b := add_dotProduct a b f
  map_smul' c a := by simp [smul_dotProduct]
def augment (a : Fin 4 → S) (Φ : Matrix (Fin 4) (Fin 3) S) : Matrix (Fin 4) (Fin 4) S :=
  Matrix.of fun r => (Fin.cons (a r) (Φ r) : Fin 4 → S)
end General
section Domain
variable {S : Type*} [CommRing S] [IsDomain S]
end Domain
section Monic
open MvPolynomial
variable {K : Type*} [CommRing K]
noncomputable abbrev xEquiv : MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
  finSuccEquiv K 2
end Monic
section Moh
open MvPolynomial
variable {A : Type*} [CommRing A]
def fvec (x y z : A) : Fin 4 → A := ![Gen.f1 x y z, Gen.f2 x y z, Gen.f3 x y z, Gen.f4 x y z]
variable (k : Type*) [Field k] [CharZero k]
abbrev S : Type _ := MvPolynomial (Fin 3) k
def J : Ideal (S k) :=
  Ideal.span {Gen.f1 (X 0) (X 1) (X 2), Gen.f2 (X 0) (X 1) (X 2),
    Gen.f3 (X 0) (X 1) (X 2), Gen.f4 (X 0) (X 1) (X 2)}
def phiMap : (Fin 3 → S k) →ₗ[S k] (Fin 4 → S k) :=
  Matrix.mulVecLin (phi (X 0) (X 1) (X 2))
def genMap : (Fin 4 → S k) →ₗ[S k] S k :=
  rowMap (fvec (X 0) (X 1) (X 2))
end Moh
end MohP3.HilbertBurch
end


