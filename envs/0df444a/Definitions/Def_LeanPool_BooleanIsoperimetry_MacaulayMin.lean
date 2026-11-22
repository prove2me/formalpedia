-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_MacaulayMin
-- name    : LeanPool_BooleanIsoperimetry_MacaulayMin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:17:28.322032+00:00
-- url     : https://prove2.me/theorems/a005ccf1-f27a-4c97-97b9-87c16d73edd3
-- title:
--   Macaulay Min
-- statement:
--   Definitions and structural lemmas for Macaulay Min, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/MacaulayMin.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
open Finset
namespace BooleanIsoperimetry
end BooleanIsoperimetry


