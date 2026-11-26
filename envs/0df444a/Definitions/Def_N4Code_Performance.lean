-- Prove2me | Definitions.Def_N4Code_Performance
-- name    : N4Code_Performance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:58:28.265014+00:00
-- url     : https://prove2.me/theorems/efc11c9d-0fa8-4748-be0a-8e88d2f12828
-- title:
--   Performance
-- statement:
--   Definitions and structural lemmas for Performance, from Shenghao Yang, Yanyan Dong (shhyang/n4code_lean; see pinned Apache-2.0 LICENSE)'s pinned N4Code: optimal finite-length block codes of size four for binary symmetric channels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
set_option autoImplicit true
open scoped BigOperators
namespace N4Code
set_option maxRecDepth 1000000
def weight (n : ℕ) (ε : ℝ) (x : ℕ) : ℝ := (1 - ε) ^ (n - x) * ε ^ x
def wordTransform {n : ℕ} (p : Equiv (Fin n) (Fin n)) (f : Fin n → Bool) (y : Word n) : Word n :=
  fun t => if f t then !(y (p t)) else y (p t)
def wordTransformInv {n : ℕ} (p : Equiv (Fin n) (Fin n)) (f : Fin n → Bool) (y : Word n) : Word n :=
  fun t => if f (p.symm t) then !(y (p.symm t)) else y (p.symm t)
def colWeight (c : Column) : ℕ := (Finset.univ.filter fun r : Fin 4 => c r = true).card
def allEvenWeights {n : ℕ} (C : Code n) : Prop := ∀ t : Fin n, Even (colWeight (C t))
end N4Code


