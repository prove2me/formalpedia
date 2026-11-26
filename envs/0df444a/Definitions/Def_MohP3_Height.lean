-- Prove2me | Definitions.Def_MohP3_Height
-- name    : MohP3_Height
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:01:55.8617+00:00
-- url     : https://prove2.me/theorems/e79fb14e-db90-5dce-abe4-e6da81693a18
-- title:
--   Height
-- statement:
--   Definitions and structural lemmas for Height, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MvPolynomial
namespace MohP3
abbrev Rsurf := MvPolynomial (Fin 2) ℚ
def sigma : R →+* Rsurf :=
  eval₂Hom C ![X 0, (X 1)^4, (X 1)^5]
def tau : Rsurf →+* T :=
  eval₂Hom Polynomial.C ![Polynomial.X^6 + Polynomial.X^31, Polynomial.X^2]
def Psurf : Ideal R := RingHom.ker sigma
end MohP3


