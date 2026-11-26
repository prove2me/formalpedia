-- Prove2me | Definitions.Def_MohP3_HeightK
-- name    : MohP3_HeightK
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:05:32.214318+00:00
-- url     : https://prove2.me/theorems/8c1e3c09-14f7-4176-9be3-f7d285355bcb
-- title:
--   Height K
-- statement:
--   Definitions and structural lemmas for Height K, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MvPolynomial
namespace MohP3
variable (k : Type*) [Field k] [CharZero k]
def sigmaK : Rk k →+* MvPolynomial (Fin 2) k :=
  eval₂Hom C ![X 0, (X 1)^4, (X 1)^5]
def tauK : MvPolynomial (Fin 2) k →+* Polynomial k :=
  eval₂Hom Polynomial.C ![Polynomial.X^6 + Polynomial.X^31, Polynomial.X^2]
def PsurfK : Ideal (Rk k) := RingHom.ker (sigmaK k)
end MohP3


