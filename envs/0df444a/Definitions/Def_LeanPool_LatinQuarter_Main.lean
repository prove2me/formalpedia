-- Prove2me | Definitions.Def_LeanPool_LatinQuarter_Main
-- name    : LeanPool_LatinQuarter_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:21:44.708205+00:00
-- url     : https://prove2.me/theorems/d83f1c11-28a8-4176-b3c7-1859a3846f2e
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Richard Bean; LeanPool contributors's pinned Critical sets in Latin squares development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Main.lean

module
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_CornerSize
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LatinQuarter
def IsCritical {n : ℕ} (P : Finset (Cell n)) (L : Square n) : Prop :=
  IsDefining P L ∧ ∀ Q : Finset (Cell n), Q ⊂ P → ¬ IsDefining Q L
noncomputable def scs (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (L : Square n) (P : Finset (Cell n)),
    IsCritical P L ∧ P.card = m}
noncomputable def scsOf {n : ℕ} (L : Square n) : ℕ :=
  sInf {m : ℕ | ∃ P : Finset (Cell n), IsCritical P L ∧ P.card = m}
end LatinQuarter


