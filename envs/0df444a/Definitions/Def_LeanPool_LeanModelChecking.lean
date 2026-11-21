-- Prove2me | Definitions.Def_LeanPool_LeanModelChecking
-- name    : LeanPool_LeanModelChecking
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:46:28.645389+00:00
-- url     : https://prove2.me/theorems/fc4bab29-d306-4bd9-bb48-66e1427badca
-- title:
--   Lean Model Checking
-- statement:
--   Definitions and structural lemmas for Lean Model Checking, from György Kurucz; maintained by LeanPool contributors's pinned Formalizations of theorems related to model checking development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking.lean

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWResult
public import Definitions.Def_LeanPool_LeanModelChecking_SafetyLivenessDecomposition
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Continuity.Init
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
set_option autoImplicit true
@[expose] public section
@[expose] public section


