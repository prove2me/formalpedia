-- Prove2me | Definitions.Def_LeanPool_CriticalPortraits_Core
-- name    : LeanPool_CriticalPortraits_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:24:12.008494+00:00
-- url     : https://prove2.me/theorems/1cd7bfce-189e-49f7-96d8-efbf9ba1557b
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from Keston Aquino-Michaels; LeanPool contributors's pinned Counting critical portraits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Core.lean

module
public import Mathlib.Data.ZMod.Basic
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
def level {N : ℕ} (m : ℕ) (i : ZMod N) : ℕ := i.val / m
def fiber {N : ℕ} (m : ℕ) (i : ZMod N) : ℕ := i.val % m
def LevelCanonical (d m : ℕ) (S : Finset (ZMod (d * m))) : Prop :=
  ∀ j < d, (S.filter (fun i => i.val / m ≤ j)).card ≤ j
instance (d m : ℕ) (S : Finset (ZMod (d * m))) : Decidable (LevelCanonical d m S) := by
  unfold LevelCanonical; infer_instance
end CriticalPortraits


