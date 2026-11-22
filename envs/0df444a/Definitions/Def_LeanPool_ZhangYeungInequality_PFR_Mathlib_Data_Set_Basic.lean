-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
-- name    : LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:21:53.715216+00:00
-- url     : https://prove2.me/theorems/968aba2d-1410-4e83-819e-7d4b4ae39834
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Data/Set/Basic.lean

module
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.ToDual
public import Mathlib.Data.Set.Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Set
variable {α : Type*} {s t : Set α}
@[simp] alias ⟨_, inter_eq_left'⟩ := inter_eq_left
@[simp] alias ⟨_, inter_eq_right'⟩ := inter_eq_right
end Set


