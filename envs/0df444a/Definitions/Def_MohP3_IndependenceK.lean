-- Prove2me | Definitions.Def_MohP3_IndependenceK
-- name    : MohP3_IndependenceK
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:56:26.225333+00:00
-- url     : https://prove2.me/theorems/af429672-d446-4978-b71f-acaa81e23de7
-- title:
--   Independence K
-- statement:
--   Definitions and structural lemmas for Independence K, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/IndependenceK.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Polynomial
namespace MohP3.K
variable (k : Type*) [Field k]
def vvK : Fin 8 → Polynomial k :=
  ![1, X ^ 6 * (1 + X ^ 25), X ^ 10, X ^ 12 * (1 + 2 * X ^ 25 + X ^ 50), X ^ 41,
    X ^ 43 * (3 + 3 * X ^ 25 + X ^ 50), X ^ 45 * (-2 - X ^ 25), X ^ 47]
def ooK : Fin 8 → ℕ := ![0, 6, 10, 12, 41, 43, 45, 47]
variable {k}
variable (k) [CharZero k]
end MohP3.K


