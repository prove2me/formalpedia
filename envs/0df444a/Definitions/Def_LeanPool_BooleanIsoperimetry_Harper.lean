-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
-- name    : LeanPool_BooleanIsoperimetry_Harper
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:17:15.131573+00:00
-- url     : https://prove2.me/theorems/80af4db1-2ee5-4e31-b03a-8ebd320f070a
-- title:
--   Harper
-- statement:
--   Definitions and structural lemmas for Harper, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
namespace BooleanIsoperimetry
noncomputable def gShiftIntervalCount (n lo hi : ℕ) : ℕ :=
  (Finset.univ.filter (fun v : Cube n => lo ≤ rank (gShift v) ∧ rank (gShift v) < hi)).card
noncomputable def boundaryCostH (N a b : ℕ) : ℕ :=
  max (H N a) b + max (H N b) a
noncomputable def boundaryCost (n a b : ℕ) : ℕ :=
  max (H n a) b + max (H n b) a
end BooleanIsoperimetry


