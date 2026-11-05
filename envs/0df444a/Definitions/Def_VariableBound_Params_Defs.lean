-- Prove2me | Definitions.Def_VariableBound_Params_Defs
-- name    : VariableBound_Params_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:45:34.849235+00:00
-- url     : https://prove2.me/theorems/eb90e5e7-a5b7-4ce0-a786-216936b0a748
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Definitions.Def_ToTuring_PolyT
import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option autoImplicit false
section
section
namespace VariableBound
open Groundwork AppVariables
noncomputable def lg (x : ℝ) : ℝ := Real.logb 2 x
def nbD (n Δ : ℕ) : ℕ := 2 ^ (((List.range (Nat.log 2 n + 1)).filter fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)).length - 1)
def rbD (β : ℕ) : ℕ := ((List.range (3 * β + 2)).filter fun j => decide (¬ 3 ^ j * 2 ^ β < 4 ^ j)).length
def tbD (m nb rb : ℕ) : ℕ := ((List.range (Nat.size m + rb + 1)).filter fun c => decide (¬ m * (15 * nb + 16) ^ rb ≤ 2 ^ c * (15 * nb) ^ rb)).length
def StParamSpec : Prop :=
  (∀ n Δ : ℕ, 1 ≤ Δ → 2 * Δ ≤ 2 ^ n → IsNb n Δ (nbD n Δ)) ∧ (∀ n Δ : ℕ, 1 ≤ Δ → (2 * Δ) ^ 2 ≤ 2 ^ n → 2 ≤ nbD n Δ) ∧
  (∀ β : ℕ, IsRb β (rbD β)) ∧ (∀ m nb rb : ℕ, 2 ≤ nb → IsTb m nb rb (tbD m nb rb))
structure ParamIneq : Prop where
  /-- for 2 ≤ Δ and m ≤ Δ·n: m/n̄ < 2Δ·log(2Δ), so s̄ = 16m/n̄ < 32Δ·log(2Δ) -/
  sb_lt : ∀ n Δ m nb : ℕ, 2 ≤ Δ → m ≤ Δ * n → IsNb n Δ nb → (m : ℝ) / nb < 2 * Δ * lg (2 * Δ) ∧ 16 * (m : ℝ) / nb < 32 * Δ * lg (2 * Δ)
  /-- for 2 ≤ Δ and m ≤ Δ·n: 3m/(n̄+1) < 6Δ·log(2Δ) ≤ (2Δ)³ -/
  three_m : ∀ n Δ m nb : ℕ, 2 ≤ Δ → m ≤ Δ * n → IsNb n Δ nb → 3 * (m : ℝ) / (nb + 1) < 6 * Δ * lg (2 * Δ) ∧ 6 * (Δ : ℝ) * lg (2 * Δ) ≤ (2 * Δ) ^ 3
  /-- for 2 ≤ Δ and n̄ < m ≤ Δ·n: β ≤ n + 3(n̄+1)·log(2Δ) + 2 ≤ 4n + 3·log(2Δ) + 2 -/
  beta_le : ∀ n Δ m nb : ℕ, 2 ≤ Δ → nb < m → m ≤ Δ * n → IsNb n Δ nb →
    (beta n m nb : ℝ) ≤ n + 3 * (nb + 1) * lg (2 * Δ) + 2 ∧ (n : ℝ) + 3 * (nb + 1) * lg (2 * Δ) + 2 ≤ 4 * n + 3 * lg (2 * Δ) + 2
  /-- for any β and the r̄ of the text (`IsRb β r̄`): r̄ ≤ 2.41·β + 1 -/
  rb_le : ∀ β rb : ℕ, IsRb β rb → (rb : ℝ) ≤ 2.41 * β + 1
  /-- display (61), for 2 ≤ Δ, n̄ < m ≤ Δ·n, the r̄ of the text and n ≥ 29·log(2Δ) + 19 (in place of
  the text's n ≥ n₀): r̄ ≤ 10n and M ≤ 14n -/
  large : ∀ n Δ m nb rb : ℕ, 2 ≤ Δ → nb < m → m ≤ Δ * n → IsNb n Δ nb → IsRb (beta n m nb) rb → 29 * lg (2 * Δ) + 19 ≤ n →
    rb ≤ 10 * n ∧ Mb (beta n m nb) rb ≤ 14 * n
  /-- for 2 ≤ Δ and any number r̄ ≤ 10n (as display (61) gives): p·r̄ < 22·log(2Δ) -/
  p_rb : ∀ n Δ nb rb : ℕ, 2 ≤ Δ → IsNb n Δ nb → rb ≤ 10 * n → ((pp nb : ℚ) : ℝ) * rb < 22 * lg (2 * Δ)
  /-- for 2 ≤ Δ, m ≥ 1, any number r̄ ≤ 10n (as display (61) gives) and the t̄ of the text for this
  r̄ (`IsTb m n̄ r̄ t̄`): t̄ ≤ log m + 33·log(2Δ) + 1 -/
  tb_le : ∀ n Δ m nb rb tb : ℕ, 2 ≤ Δ → 1 ≤ m → IsNb n Δ nb → rb ≤ 10 * n → IsTb m nb rb tb → (tb : ℝ) ≤ lg m + 33 * lg (2 * Δ) + 1
def StCertParam : Prop := ∀ (α : Type) [Enc α] (n Δ m β nb rb : α → ℕ), Unary n → Unary Δ → Unary m → Unary β → Unary nb → Unary rb →
  (Unary fun x => nbD (n x) (Δ x)) ∧ (Unary fun x => beta (n x) (m x) (nb x)) ∧ (Unary fun x => rbD (β x)) ∧ (Unary fun x => tbD (m x) (nb x) (rb x))
end VariableBound


