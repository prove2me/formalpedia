-- Prove2me | Definitions.Def_LeanPool_CriticalPortraits
-- name    : LeanPool_CriticalPortraits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:32:00.795964+00:00
-- url     : https://prove2.me/theorems/0c35711e-3504-4497-a3a3-28456ac7f7ff
-- title:
--   Critical Portraits
-- statement:
--   Definitions and structural lemmas for Critical Portraits, from Keston Aquino-Michaels; LeanPool contributors's pinned Counting critical portraits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits.lean

module
public import Definitions.Def_LeanPool_CriticalPortraits_CycleLemma
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Denominator
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
public import Definitions.Def_LeanPool_CriticalPortraits_Census
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


