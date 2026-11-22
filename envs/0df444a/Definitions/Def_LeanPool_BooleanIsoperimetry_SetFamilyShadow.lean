-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_SetFamilyShadow
-- name    : LeanPool_BooleanIsoperimetry_SetFamilyShadow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:17:11.968521+00:00
-- url     : https://prove2.me/theorems/673cedc0-4ab9-437b-91bc-5f577e6e03bc
-- title:
--   Set Family Shadow
-- statement:
--   Definitions and structural lemmas for Set Family Shadow, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SetFamilyShadow.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
open Finset
namespace BooleanIsoperimetry
end BooleanIsoperimetry


