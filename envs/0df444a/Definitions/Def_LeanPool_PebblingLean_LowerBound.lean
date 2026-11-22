-- Prove2me | Definitions.Def_LeanPool_PebblingLean_LowerBound
-- name    : LeanPool_PebblingLean_LowerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:49:55.249813+00:00
-- url     : https://prove2.me/theorems/3c8ba764-8190-4bac-b326-158072be6f02
-- title:
--   Lower Bound
-- statement:
--   Definitions and structural lemmas for Lower Bound, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Definitions.Def_LeanPool_PebblingLean_Weight
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
namespace Hypercube
open Pebbling
end Hypercube
end PebblingLean


