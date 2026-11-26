-- Prove2me | Definitions.Def_MohP3_GlobalK
-- name    : MohP3_GlobalK
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:01:25.762802+00:00
-- url     : https://prove2.me/theorems/0801cd67-f8fb-43f4-9999-4278c16c413a
-- title:
--   Global K
-- statement:
--   Definitions and structural lemmas for Global K, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MvPolynomial
namespace MohP3
variable (k : Type*) [Field k] [CharZero k]
abbrev Rk := MvPolynomial (Fin 3) k
def xk : Rk k := X 0
def yk : Rk k := X 1
def zk : Rk k := X 2
def Ppoly : Ideal (Rk k) := Gen.P (xk k) (yk k) (zk k)
def Qpoly : Ideal (Rk k) := Gen.Q (xk k) (yk k) (zk k)
def rho_k : Rk k →+* Polynomial k :=
  eval₂Hom Polynomial.C ![Polynomial.X ^ 6 + Polynomial.X ^ 31, Polynomial.X ^ 8,
    Polynomial.X ^ 10]
def hhK (i : Fin 8) : Rk k := Gen.hh (xk k) (yk k) (zk k) i
def ffK (j : Fin 4) : Rk k := Gen.ff (xk k) (yk k) (zk k) j
def iotaK : Polynomial k →+* Rk k := Polynomial.eval₂RingHom MvPolynomial.C (yk k)
def qxPoly (i j : Fin 8) : Polynomial k :=
  Polynomial.C (((Gen.qxD i j).1 : k)) * Polynomial.X ^ (Gen.qxD i j).2
def qzPoly (i j : Fin 8) : Polynomial k :=
  Polynomial.C (((Gen.qzD i j).1 : k)) * Polynomial.X ^ (Gen.qzD i j).2
def RepP (g : Rk k) : Prop :=
  ∃ (p : Fin 8 → Polynomial k) (c : Fin 4 → Rk k),
    g = (∑ i, iotaK k (p i) * hhK k i) + ∑ j, c j * ffK k j
end MohP3


