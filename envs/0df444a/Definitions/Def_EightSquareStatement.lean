-- Prove2me | Definitions.Def_EightSquareStatement
-- name    : EightSquareStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:27:36.316132+00:00
-- url     : https://prove2.me/theorems/f652c74f-2966-401d-bf64-9fb72316f703
-- title:
--   Eight Square Statement
-- statement:
--   Definitions and structural lemmas for Eight Square Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/EightSquareStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesStatement
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
set_option autoImplicit false
section
section
namespace Eight
open Finset Polynomial
abbrev Block : Type := Bool × Bool × Bool
def bxor (p q : Block) : Block := (p.1 ^^ q.1, p.2.1 ^^ q.2.1, p.2.2 ^^ q.2.2)
def phi (p q : Block) : ℕ :=
  p.1.toNat * q.1.toNat + p.1.toNat * q.2.1.toNat + p.1.toNat * q.2.2.toNat + p.2.1.toNat * q.2.1.toNat + p.2.1.toNat * q.2.2.toNat
    + p.2.2.toNat * q.2.2.toNat
    + q.1.toNat * p.2.1.toNat * p.2.2.toNat + p.1.toNat * q.2.1.toNat * p.2.2.toNat + p.1.toNat * p.2.1.toNat * q.2.2.toNat
def sigma (p q : Block) : ℤ := (-1) ^ phi p q
def Signs : Prop := ∀ p q p' q' : Block, bxor p q = bxor p' q' → q ≠ q' → sigma p q * sigma p' q' + sigma p q' * sigma p' q = 0
def psi (k p q : Block) : ℤ := if bxor p q = k then sigma p q else 0
def Rb (x y u v : Block) : ℤ := ∑ k, psi k x y * psi k v u
def Cb (x y u v : Block) : ℤ := ∑ k, psi k x u * psi k v y
def FactorsLe {Z Z' : Type} (F : Z → Z' → ℤ) (c : ℕ) (b : ℤ) : Prop :=
  ∃ (f : Z → Pieces.Bits c → ℤ) (f' : Z' → Pieces.Bits c → ℤ),
    (∀ z z', F z z' = ∑ θ, f z θ * f' z' θ) ∧ (∀ z θ, |f z θ| ≤ b) ∧ ∀ z' θ, |f' z' θ| ≤ b
def tOf (lam : ℕ) : ℕ := (lam + 2) / 3
def bitAt {lam : ℕ} (x : Pieces.Bits lam) (j : ℕ) : Bool := if h : j < lam then x ⟨j, h⟩ else false
def blockAt {lam : ℕ} (x : Pieces.Bits lam) (s : ℕ) : Block := (bitAt x (3 * s), bitAt x (3 * s + 1), bitAt x (3 * s + 2))
noncomputable def prodRC {lam : ℕ} (x y u v : Pieces.Bits lam) : ℤ[X] :=
  ∏ s ∈ range (tOf lam), (C (Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s)) + X * C (Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s)))
noncomputable def A (lam i : ℕ) : Pieces.Four lam := fun x y u v => (prodRC x y u v).coeff i
def crow (lam i : ℕ) : ℕ := min (2 * lam) (4 * tOf lam + 3 * i)
def ccol (lam i : ℕ) : ℕ := min (2 * lam) (7 * tOf lam - 3 * i)
noncomputable def rho : ℝ := 11 / 12
structure LemPieces : Prop where
  a_sum : ∀ lam : ℕ, 1 ≤ lam → ∀ x y u v : Pieces.Bits lam, ∑ i ∈ range (tOf lam + 1), A lam i x y u v = 2 ^ tOf lam * Pieces.cross x y u v
  a_abs : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ∀ x y u v : Pieces.Bits lam, |A lam i x y u v| ≤ 2 ^ tOf lam
  b_row : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → FactorsLe (Pieces.rowwise (A lam i)) (crow lam i) (2 ^ tOf lam)
  b_col : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → FactorsLe (Pieces.colwise (A lam i)) (ccol lam i) (2 ^ tOf lam)
  c_row : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → crow lam i ≤ 2 * lam
  c_col : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ccol lam i ≤ 2 * lam
  /-- from the proof of (c): c_i^row + c_i^col ≤ 11t -/
  c_sum_t : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → crow lam i + ccol lam i ≤ 11 * tOf lam
  c_sum : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ((crow lam i + ccol lam i : ℕ) : ℝ) ≤ 4 * rho * lam + 8
end Eight


