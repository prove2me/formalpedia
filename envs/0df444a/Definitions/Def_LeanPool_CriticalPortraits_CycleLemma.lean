-- Prove2me | Definitions.Def_LeanPool_CriticalPortraits_CycleLemma
-- name    : LeanPool_CriticalPortraits_CycleLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:24:13.418497+00:00
-- url     : https://prove2.me/theorems/fdc72a71-defc-4ca2-9919-9f89958a491b
-- title:
--   Cycle Lemma
-- statement:
--   Definitions and structural lemmas for Cycle Lemma, from Keston Aquino-Michaels; LeanPool contributors's pinned Counting critical portraits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/CycleLemma.lean

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CriticalPortraits.Cycle
variable {n : ℕ}
def Q (a : ℕ → ℤ) (k : ℕ) : ℤ := ∑ j ∈ Finset.range k, a j
def Good (n : ℕ) (a : ℕ → ℤ) (i : ℕ) : Prop := ∀ t, i < t → t < i + n → Q a i < Q a t
end CriticalPortraits.Cycle


