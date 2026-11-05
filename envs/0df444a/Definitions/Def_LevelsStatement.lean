-- Prove2me | Definitions.Def_LevelsStatement
-- name    : LevelsStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:17:57.155074+00:00
-- url     : https://prove2.me/theorems/3e054b32-3827-4da3-925b-602c876252ac
-- title:
--   Levels Statement
-- statement:
--   Definitions and structural lemmas for Levels Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/LevelsStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
set_option autoImplicit false
section
section
namespace Levels
namespace Gen
def K (x₀ : ℕ) : ℕ → ℕ
  | 0 => 2 ^ x₀
  | l + 1 => (2 ^ (3 * l + x₀) * K x₀ l) ^ 2
def g (x₀ l : ℕ) : ℕ := 2 ^ (3 * l + x₀) * K x₀ l
noncomputable def zeta (l : ℕ) : ℝ := 1 / 2 ^ (l + 5)
noncomputable def e (ρ : ℝ) (x₀ : ℕ) : ℕ → ℝ
  | 0 => 1 / 2
  | l + 1 => (ρ + 3 * zeta l) * e ρ x₀ l + 3 / K x₀ l
structure PartA : Prop where
  logK : ∀ x₀ l : ℕ, Real.logb 2 (K x₀ l) = (3 * x₀ + 6) * 2 ^ l - 6 * l - 2 * x₀ - 6
  K_lt : ∀ x₀ l : ℕ, 18 ≤ x₀ → K x₀ l < K x₀ (l + 1)
  K_le : ∀ x₀ l : ℕ, 18 ≤ x₀ → K x₀ (l + 1) ≤ K x₀ l ^ 10
  e_ge : ∀ (ρ : ℝ) (x₀ l : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 18 ≤ x₀ → ρ ^ l / 2 ≤ e ρ x₀ l
  e_le : ∀ (ρ : ℝ) (x₀ l : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 18 ≤ x₀ → e ρ x₀ l ≤ 0.85 * ρ ^ l
  rho_pow : ∀ (ρ : ℝ) (x₀ l : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 18 ≤ x₀ →
    ρ ^ l ≤ ((3 * x₀ + 6) / Real.logb 2 (K x₀ l)) ^ Real.logb 2 (1 / ρ)
  /-- the condition of case (ii) of Lemma 8 at every level -/
  case_ii : ∀ x₀ l : ℕ, 18 ≤ x₀ → (K x₀ l : ℝ) * Real.log (2 * g x₀ l * K x₀ l) ≤ 2 * zeta l ^ 2 * g x₀ l
end Gen
namespace Thin
end Thin
end Levels


