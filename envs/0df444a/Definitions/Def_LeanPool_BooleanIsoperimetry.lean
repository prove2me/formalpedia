-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry
-- name    : LeanPool_BooleanIsoperimetry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:41:19.933959+00:00
-- url     : https://prove2.me/theorems/9f7042a3-1e98-4bb1-bf24-833fecc7fc42
-- title:
--   Boolean Isoperimetry
-- statement:
--   Definitions and structural lemmas for Boolean Isoperimetry, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyOrderBridge
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Definitions.Def_LeanPool_BooleanIsoperimetry_MacaulayMin
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SetFamilyShadow
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
set_option autoImplicit true
@[expose] public section
@[expose] public section


