-- Prove2me | Definitions.Def_LeanPool_NashWilliams_Order
-- name    : LeanPool_NashWilliams_Order
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:42:49.347202+00:00
-- url     : https://prove2.me/theorems/5cbcc067-1abb-4be9-8448-64244ca9da15
-- title:
--   Order
-- statement:
--   Definitions and structural lemmas for Order, from Yann Pequignot; LeanPool contributors's pinned Nash-Williams fronts and better-quasi-orders development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order.lean

module
public import Definitions.Def_LeanPool_NashWilliams_Order_TwoBQO
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
set_option autoImplicit true
@[expose] public section
@[expose] public section


