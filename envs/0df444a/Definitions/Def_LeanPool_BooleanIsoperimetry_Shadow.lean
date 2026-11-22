-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
-- name    : LeanPool_BooleanIsoperimetry_Shadow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:16:35.239525+00:00
-- url     : https://prove2.me/theorems/91508245-57c7-4a70-bf23-65018b81d7b4
-- title:
--   Shadow
-- statement:
--   Definitions and structural lemmas for Shadow, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
namespace BooleanIsoperimetry
noncomputable def upperShadow (N r t : ℕ) : ℕ :=
  H N (binomPrefix N r + t) - binomPrefix N (r + 1)
end BooleanIsoperimetry


