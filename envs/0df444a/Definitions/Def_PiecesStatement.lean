-- Prove2me | Definitions.Def_PiecesStatement
-- name    : PiecesStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:27:08.260818+00:00
-- url     : https://prove2.me/theorems/6e12a701-a31b-46a6-9926-fe73bc4fadb4
-- title:
--   Pieces Statement
-- statement:
--   Definitions and structural lemmas for Pieces Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/PiecesStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Fintype.BigOperators
set_option autoImplicit false
section
section
namespace Pieces
open Finset Polynomial
abbrev Bits (n : ℕ) : Type := Fin n → Bool
abbrev Four (n : ℕ) : Type := Bits n → Bits n → Bits n → Bits n → ℤ
def cross {n : ℕ} : Four n := fun x y u v => if x = v ∧ y = u then 1 else 0
def FactorsThrough {X X' : Type} (F : X → X' → ℤ) (c : ℕ) (b : ℤ) : Prop :=
  ∃ (f : X → Bits c → ℤ) (f' : X' → Bits c → ℤ),
    (∀ z z', F z z' = ∑ θ, f z θ * f' z' θ) ∧ (∀ z θ, |f z θ| < b) ∧ ∀ z' θ, |f' z' θ| < b
def rowwise {n : ℕ} (A : Four n) : Bits n × Bits n → Bits n × Bits n → ℤ := fun p q => A p.1 p.2 q.1 q.2
def colwise {n : ℕ} (A : Four n) : Bits n × Bits n → Bits n × Bits n → ℤ := fun p q => A p.1 q.1 p.2 q.2
structure Family (lam : ℕ) where
  d : ℤ
  I : Finset ℤ
  A : ℤ → Four lam
  crow : ℤ → ℕ
  ccol : ℤ → ℕ
structure Family.Is {lam : ℕ} (P : Family lam) (ρ : ℝ) (c : ℕ) : Prop where
  d_pos : 1 ≤ P.d
  sum_eq : ∀ x y u v, ∑ i ∈ P.I, P.A i x y u v = P.d * cross x y u v
  row : ∀ i ∈ P.I, FactorsThrough (rowwise (P.A i)) (P.crow i) (2 ^ (2 * lam) ^ c)
  col : ∀ i ∈ P.I, FactorsThrough (colwise (P.A i)) (P.ccol i) (2 ^ (2 * lam) ^ c)
  caps : ∀ i ∈ P.I, ((P.crow i + P.ccol i : ℕ) : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam)
  card_I : #P.I ≤ (2 * lam) ^ c
  abs_d : P.d < 2 ^ (2 * lam) ^ c
  abs_I : ∀ i ∈ P.I, |i| < 2 ^ (2 * lam) ^ c
  abs_A : ∀ i ∈ P.I, ∀ x y u v, |P.A i x y u v| < 2 ^ (2 * lam) ^ c
section Blocks
abbrev Lab (n : ℕ) : Type := Fin n → Bool × Bool
variable (n h : ℕ)
def nblk : ℕ := (n + h - 1) / h
def blk (b : ℕ) : Finset (Fin n) := univ.filter fun k => k.val / h = b
variable {n}
def odd (β : Lab n) : ℕ := #{b ∈ range (nblk n h) | Odd #{k ∈ blk n h b | β k = (true, true)}}
variable (n)
def mu : ℕ := (∑ β : Lab n, odd h β) / 4 ^ n
variable {n}
variable (n)
end Blocks
end Pieces


