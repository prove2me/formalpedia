-- Prove2me | Definitions.Def_LeanPool_RungeKuttaOrderConditions
-- name    : LeanPool_RungeKuttaOrderConditions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:58:46.346021+00:00
-- url     : https://prove2.me/theorems/faac3bb8-a954-4b83-8739-a5c3ea56cdaa
-- title:
--   Runge Kutta Order Conditions
-- statement:
--   Definitions and structural lemmas for Runge Kutta Order Conditions, from Carles Marín; LeanPool contributors's pinned Certified Runge-Kutta order conditions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions.lean

module
public import Definitions.Def_LeanPool_RungeKuttaOrderConditions_ButcherOrder
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
set_option autoImplicit true
@[expose] public section
@[expose] public section


