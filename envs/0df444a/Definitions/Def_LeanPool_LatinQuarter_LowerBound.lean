-- Prove2me | Definitions.Def_LeanPool_LatinQuarter_LowerBound
-- name    : LeanPool_LatinQuarter_LowerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:21:20.477603+00:00
-- url     : https://prove2.me/theorems/d4f5e733-be78-40c0-8c68-60a019d8bc8e
-- title:
--   Lower Bound
-- statement:
--   Definitions and structural lemmas for Lower Bound, from Richard Bean; LeanPool contributors's pinned Critical sets in Latin squares development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/LowerBound.lean

module
public import Definitions.Def_LeanPool_LatinQuarter_Counting
public import Definitions.Def_LeanPool_LatinQuarter_Shifted
public import Definitions.Def_LeanPool_LatinQuarter_Budget
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial
end LatinQuarter


