-- Prove2me | Definitions.Def_LeanPool_LatinQuarter_SquareZero
-- name    : LeanPool_LatinQuarter_SquareZero
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:08.110769+00:00
-- url     : https://prove2.me/theorems/4e7118c4-8c89-470e-a4ab-47859f40f561
-- title:
--   Square Zero
-- statement:
--   Definitions and structural lemmas for Square Zero, from Richard Bean; LeanPool contributors's pinned Critical sets in Latin squares development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/SquareZero.lean

module
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Algebra.Operations
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LatinQuarter
open scoped BigOperators Pointwise
variable {R : Type*} [CommRing R]
end LatinQuarter


