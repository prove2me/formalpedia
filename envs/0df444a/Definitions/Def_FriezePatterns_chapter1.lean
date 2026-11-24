-- Prove2me | Definitions.Def_FriezePatterns_chapter1
-- name    : FriezePatterns_chapter1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:08:59.673484+00:00
-- url     : https://prove2.me/theorems/3ff633a3-e13a-4601-8011-a263f8614ed0
-- title:
--   chapter1
-- statement:
--   Definitions and structural lemmas for chapter1, from Antoine-dSG (Antoine-dSG/frieze_patterns; see pinned Apache-2.0 LICENSE)'s pinned Fibonacci upper bound and attainment for arithmetic frieze patterns development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Antoine-dSG/frieze_patterns/blob/4e921473387f925942f0b95f3853c59b33670282/FriezePatterns/chapter1.lean

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
set_option autoImplicit true
class pattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) : Prop where
  topBordZeros : ∀ m, f (0,m) = 0
  topBordOnes : ∀ m, f (1,m) =1
  botBordOnes_n : ∀ m, f (n, m) = 1
  botBordZeros_n : ∀ i, ∀ m,  i ≥ n+1 → (f (i,m) = 0)
  diamond : ∀ i, ∀ m,  i ≤ n-1 → f (i+1,m) * f (i+1,m+1)-1 = f (i+2,m)*f (i,m+1)
class nzPattern_n (F : Type*) [Field F] (f : ℕ × ℕ → F) (n : ℕ) extends pattern_n F f n where
  non_zero : ∀ i, ∀ m, 1 ≤ i ∧ i ≤ n → f (i,m) ≠ 0


