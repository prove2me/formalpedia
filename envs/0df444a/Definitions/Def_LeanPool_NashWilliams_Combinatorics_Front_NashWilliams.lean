-- Prove2me | Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_NashWilliams
-- name    : LeanPool_NashWilliams_Combinatorics_Front_NashWilliams
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:43:39.817291+00:00
-- url     : https://prove2.me/theorems/32770907-87fa-4bfa-be3d-d0bdc4e44142
-- title:
--   Nash Williams
-- statement:
--   Definitions and structural lemmas for Nash Williams, from Yann Pequignot; LeanPool contributors's pinned Nash-Williams fronts and better-quasi-orders development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/NashWilliams.lean

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Shrink
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Ray
public import Definitions.Def_LeanPool_NashWilliams_Data_Fintype_Pigeonhole
public import Definitions.Def_LeanPool_NashWilliams_Data_Nat_Nth
public import Mathlib.Data.Finset.Sort
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set List
noncomputable section
namespace Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
end Front


