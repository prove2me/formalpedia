-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Insert
-- name    : LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Insert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:43:32.098037+00:00
-- url     : https://prove2.me/theorems/8e82c102-a21d-44e1-9b2d-dfecd92373f8
-- title:
--   Insert
-- statement:
--   Definitions and structural lemmas for Insert, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Data/Set/Insert.lean

module
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Set
variable {α : Type*} {s t : Set α}
alias ⟨_, inter_singleton_eq_empty'⟩ := inter_singleton_eq_empty
alias ⟨_, singleton_inter_eq_empty'⟩ := singleton_inter_eq_empty
end Set


