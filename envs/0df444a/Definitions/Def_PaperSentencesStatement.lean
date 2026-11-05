-- Prove2me | Definitions.Def_PaperSentencesStatement
-- name    : PaperSentencesStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:24:24.693838+00:00
-- url     : https://prove2.me/theorems/527adc5d-e5c7-4a5a-9c88-d7c6603bbb54
-- title:
--   Paper Sentences Statement
-- statement:
--   Definitions and structural lemmas for Paper Sentences Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/PaperSentencesStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option autoImplicit false
section
section
namespace PaperSentences
open Turing
open Sat3 (CNF)
open scoped ENNReal
noncomputable def lg (x : ℝ) : ℝ := Real.logb 2 x
def DecidesInTime (k n₀ : ℕ) (T : ℕ → ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ SatK.DecidesTM k M t ∧ ∀ n : ℕ, n₀ ≤ n → (t n : ℝ) ≤ T n
def CountsInTime (k n₀ : ℕ) (T : ℕ → ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ SatK.CountsTM k M t ∧ ∀ n : ℕ, n₀ ≤ n → (t n : ℝ) ≤ T n
def ThmEveryDelta : Prop := ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, DecidesInTime 3 0 fun n => C * (2 : ℝ) ^ (δ * n)
noncomputable def sInfty : ℝ≥0∞ := ⨆ (k : ℕ) (_ : 3 ≤ k), SatK.sTM k
def ETH : Prop := ∀ k : ℕ, 3 ≤ k → 0 < SatK.sTM k
def SETH : Prop := sInfty = 1
def CorEth : Prop := (∀ k : ℕ, 3 ≤ k → SatK.sTM k = 0) ∧ sInfty = 0 ∧ ¬ ETH ∧ ¬ SETH
def CorCounting : Prop :=
  (∀ k : ℕ, 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, CountsInTime k 0 fun n => C * (2 : ℝ) ^ (δ * n)) ∧ ¬ SatK.CountETH_TM
def CountRate (c : ℝ) : Prop := ∃ C : ℝ, CountsInTime 3 2 fun n => (2 : ℝ) ^ (C * (n / lg n ^ c))
end PaperSentences


