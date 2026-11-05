-- Prove2me | Definitions.Def_GeneralPieces_Num_PartA
-- name    : GeneralPieces_Num_PartA
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:33:44.441212+00:00
-- url     : https://prove2.me/theorems/1c9d2e75-049d-481b-a53b-2fee427de8c8
-- title:
--   Part A
-- statement:
--   Definitions and structural lemmas for Part A, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Theorems.Thm_ClauseBound_Gen_K_eq

set_option autoImplicit false
section
section
namespace GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen
theorem x_succ (x₀ l : ℕ) : x x₀ (l + 1) = 2 * x x₀ l + 6 * l + 2 * x₀ := by
  rw [x]; ring
theorem x_ge_pow (x₀ l : ℕ) : 2 ^ l * x₀ ≤ x x₀ l := by
  induction l with
  | zero => simp [x]
  | succ l ih =>
    have h : 2 ^ (l + 1) * x₀ = 2 * (2 ^ l * x₀) := by ring
    rw [x_succ, h]; omega
theorem pow_ge_max (x₀ l : ℕ) (hx : 1 ≤ x₀) : max l x₀ ≤ 2 ^ l * x₀ := by
  have h1 : l < 2 ^ l := Nat.lt_two_pow_self
  have h2 : 2 ^ l * 1 ≤ 2 ^ l * x₀ := Nat.mul_le_mul_left _ hx
  have h3 : 1 * x₀ ≤ 2 ^ l * x₀ := Nat.mul_le_mul_right _ Nat.one_le_two_pow
  exact max_le (by omega) (by omega)
theorem x_succ_le (x₀ l : ℕ) (hx : 1 ≤ x₀) : x x₀ (l + 1) ≤ 10 * x x₀ l := by
  have h := le_trans (pow_ge_max x₀ l hx) (x_ge_pow x₀ l)
  have h1 : l ≤ x x₀ l := le_trans (le_max_left _ _) h
  have h2 : x₀ ≤ x x₀ l := le_trans (le_max_right _ _) h
  rw [x_succ]; omega
theorem x_lt_succ (x₀ l : ℕ) (hx : 1 ≤ x₀) : x x₀ l < x x₀ (l + 1) := by
  rw [x_succ]; omega
theorem K_lt_le (x₀ l : ℕ) (hx : 1 ≤ x₀) : K x₀ l < K x₀ (l + 1) ∧ K x₀ (l + 1) ≤ K x₀ l ^ 10 := by
  rw [K_eq, K_eq, ← pow_mul]
  exact ⟨Nat.pow_lt_pow_right (by norm_num) (x_lt_succ x₀ l hx),
    Nat.pow_le_pow_right (by norm_num) (by have := x_succ_le x₀ l hx; omega)⟩
noncomputable def y (ρ : ℝ) (x₀ l : ℕ) : ℝ := e ρ x₀ l / ρ ^ l
structure TheoremAa (ρ : ℝ) (x₀ : ℕ) : Prop where
  /-- log K_ℓ = (3x₀+6)·2^ℓ − 6ℓ − 2x₀ − 6 -/
  logK : ∀ l : ℕ, Real.logb 2 (K x₀ l) = (3 * x₀ + 6) * 2 ^ l - 6 * l - 2 * x₀ - 6
  /-- so K_ℓ < K_{ℓ+1} ≤ K_ℓ^10 -/
  K_lt_le : ∀ l : ℕ, K x₀ l < K x₀ (l + 1) ∧ K x₀ (l + 1) ≤ K x₀ l ^ 10
  /-- ρ^ℓ/2 ≤ e_ℓ ≤ 0.85·ρ^ℓ -/
  e_bounds : ∀ l : ℕ, 1 / 2 * ρ ^ l ≤ e ρ x₀ l ∧ e ρ x₀ l ≤ 0.85 * ρ ^ l
  /-- where ρ^ℓ ≤ ((3x₀+6)/log K_ℓ)^{α'}, α' = log(1/ρ) -/
  rho_pow : ∀ l : ℕ, ρ ^ l ≤ ((3 * x₀ + 6) / Real.logb 2 (K x₀ l)) ^ Real.logb 2 (1 / ρ)
end GeneralPieces.PartA


