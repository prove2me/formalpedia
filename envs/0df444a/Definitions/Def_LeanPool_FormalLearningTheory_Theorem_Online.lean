-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Online
-- name    : LeanPool_FormalLearningTheory_Theorem_Online
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:33:38.698869+00:00
-- url     : https://prove2.me/theorems/b6ab8e84-927d-47bd-ad2c-997d71fcab45
-- title:
--   Online
-- statement:
--   Definitions and structural lemmas for Online, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Online.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
set_option autoImplicit true
@[expose] public section
@[expose] public section
def LTree.truncate {X : Type} {n m : ℕ} : (h : n ≤ m) → LTree X m → LTree X n := by
  intro h T; induction n generalizing m with
  | zero => exact .leaf
  | succ k ih =>
    match m, T, h with
    | _ + 1, .branch x l r, h =>
      exact .branch x (ih (Nat.le_of_succ_le_succ h) l) (ih (Nat.le_of_succ_le_succ h) r)


