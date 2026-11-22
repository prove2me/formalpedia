-- Prove2me | Definitions.Def_LeanPool_CriticalPortraits_Census
-- name    : LeanPool_CriticalPortraits_Census
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:29:59.175861+00:00
-- url     : https://prove2.me/theorems/31e594b5-d2d0-4a3a-b9ff-5ca8344c7d45
-- title:
--   Census
-- statement:
--   Definitions and structural lemmas for Census, from Keston Aquino-Michaels; LeanPool contributors's pinned Counting critical portraits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Census.lean

module
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Definitions.Def_LeanPool_CriticalPortraits_Denominator
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CriticalPortraits
open Finset
end CriticalPortraits


