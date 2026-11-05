-- Prove2me | Definitions.Def_CliqueLevelsStatement
-- name    : CliqueLevelsStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:30:15.151067+00:00
-- url     : https://prove2.me/theorems/bc5032a2-f868-4063-831c-af0f42c4ca56
-- title:
--   Clique Levels Statement
-- statement:
--   Definitions and structural lemmas for Clique Levels Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/CliqueLevelsStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedStatement
set_option autoImplicit false
section
section
namespace CliqueLevels
open Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed
noncomputable def bound (e : ℝ) (K C₀ lam B : ℕ) : ℝ := (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * lam) * ((K : ℝ) * ((lam : ℝ) + B)) ^ (C₀ * K ^ 2)
def Solves (M : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) : Prop :=
  ∀ (l lam B : ℕ) (W : ℕ → List Bool → ℤ), 1 ≤ lam → 1 ≤ B → (∀ w < K l, ∀ z ∈ words ((K l - 1) * lam), |W w z| < 2 ^ B) →
    ∃ T S : ℕ, M.Within (tables (K l) lam W) QueryMachine.unitCost (unary l, unary lam, unary B) T S (clique (K l) lam fun w => W w.val).value ∧
      (T : ℝ) ≤ bound (e l) (K l) C₀ lam B ∧ (S : ℝ) ≤ bound (e l) (K l) C₀ lam B
noncomputable def factor (K C₀ lam B : ℕ) : ℝ := ((K : ℝ) * ((lam : ℝ) + B)) ^ (C₀ * K ^ 2)
def SolvesInFactor (M : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) : Prop :=
  ∀ (l lam B : ℕ) (W : ℕ → List Bool → ℤ), 1 ≤ lam → 1 ≤ B → (∀ w < K l, ∀ z ∈ words ((K l - 1) * lam), |W w z| < 2 ^ B) →
    ∃ T S : ℕ, M.Within (tables (K l) lam W) QueryMachine.unitCost (unary l, unary lam, unary B) T S (clique (K l) lam fun w => W w.val).value ∧
      (T : ℝ) ≤ bound (e l) (K l) C₀ lam B ∧ (S : ℝ) ≤ factor (K l) C₀ lam B
def SolvesOfSolvesInFactor : Prop := ∀ (M : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ), (∀ l, 0 ≤ e l) → SolvesInFactor M K e C₀ → Solves M K e C₀
structure Levels (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) : Prop where
  C₀_pos : 1 ≤ C₀
  K_two : ∀ l, 2 ≤ K l
  K_lt : ∀ l, K l < K (l + 1)
  K_le : ∀ l, K (l + 1) ≤ K l ^ C₀
  e_ge : ∀ l, 1 / Real.logb 2 (K l) ^ C₀ ≤ e l
  e_le : ∀ l, e l ≤ 1
def ComputesLevels (K : ℕ → ℕ) (kf : List Unit × List Unit → Option (List Unit)) : Prop :=
  PolyT kf ∧ ∀ l b : ℕ, kf (unary l, unary b) = if K l ≤ b then some (unary (K l)) else none
def NumberBetween (K : ℕ → ℕ) (e : ℕ → ℝ) (num : List Unit × List Unit → ℕ × ℕ) : Prop :=
  PolyT num ∧ ∀ l : ℕ, e l ≤ ((num (unary l, unary (K l))).1 : ℝ) / ((num (unary l, unary (K l))).2 : ℝ) ∧ ((num (unary l, unary (K l))).1 : ℝ) / ((num (unary l, unary (K l))).2 : ℝ) ≤ 2 * e l
noncomputable def cutNumber (K : ℕ → ℕ) (num : List Unit × List Unit → ℕ × ℕ) (l : ℕ) : ℝ := min (((num (unary l, unary (K l))).1 : ℝ) / ((num (unary l, unary (K l))).2 : ℝ)) 1
end CliqueLevels


