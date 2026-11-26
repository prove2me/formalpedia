-- Prove2me | Definitions.Def_MohP3_Independence
-- name    : MohP3_Independence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:44:08.515356+00:00
-- url     : https://prove2.me/theorems/d7b3373e-3659-58b7-b4d2-7b1b4dc7c1db
-- title:
--   Independence
-- statement:
--   Definitions and structural lemmas for Independence, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Polynomial
namespace MohP3
def vv : Fin 8 → ℚ[X] :=
  ![1, X^6*(1+X^25), X^10, X^12*(1+2*X^25+X^50), X^41, X^43*(3+3*X^25+X^50),
    X^45*(-2-X^25), X^47]
def oo : Fin 8 → ℕ := ![0, 6, 10, 12, 41, 43, 45, 47]
end MohP3


