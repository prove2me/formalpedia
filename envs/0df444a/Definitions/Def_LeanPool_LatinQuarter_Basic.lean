-- Prove2me | Definitions.Def_LeanPool_LatinQuarter_Basic
-- name    : LeanPool_LatinQuarter_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:08.607181+00:00
-- url     : https://prove2.me/theorems/5de22f79-85db-4e42-b47c-63910411f7d3
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Richard Bean; LeanPool contributors's pinned Critical sets in Latin squares development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Basic.lean

module
public import Mathlib.Data.Fintype.Pi
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LatinQuarter
abbrev Cell (n : ℕ) := Fin n × Fin n
abbrev Square (n : ℕ) := Fin n → Fin n → Fin n
def IsLatin {n : ℕ} (L : Square n) : Prop :=
  (∀ r, Function.Bijective (L r)) ∧
  (∀ c, Function.Bijective (fun r => L r c))
def Agrees {n : ℕ} (P : Finset (Cell n)) (L M : Square n) : Prop :=
  ∀ p ∈ P, M p.1 p.2 = L p.1 p.2
def IsDefining {n : ℕ} (P : Finset (Cell n)) (L : Square n) : Prop :=
  IsLatin L ∧ ∀ M, IsLatin M → Agrees P L M → M = L
noncomputable def completions {n : ℕ} (P : Finset (Cell n))
    (L : Square n) : Finset (Square n) := by
  classical
  exact Finset.univ.filter (fun M => IsLatin M ∧ Agrees P L M)
end LatinQuarter


