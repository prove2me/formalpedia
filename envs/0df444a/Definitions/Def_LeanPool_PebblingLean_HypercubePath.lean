-- Prove2me | Definitions.Def_LeanPool_PebblingLean_HypercubePath
-- name    : LeanPool_PebblingLean_HypercubePath
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:49:58.804812+00:00
-- url     : https://prove2.me/theorems/eb3ea612-8c5c-4980-8916-c9f5b4001cab
-- title:
--   Hypercube Path
-- statement:
--   Definitions and structural lemmas for Hypercube Path, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubePath.lean

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
namespace Hypercube
open Pebbling
end Hypercube
end PebblingLean


