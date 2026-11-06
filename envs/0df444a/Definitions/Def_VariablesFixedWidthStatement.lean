-- Prove2me | Definitions.Def_VariablesFixedWidthStatement
-- name    : VariablesFixedWidthStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:00:59.9558+00:00
-- url     : https://prove2.me/theorems/61d02a55-38c2-42c4-beb2-fd2b4349369c
-- title:
--   Variables Fixed Width Statement
-- statement:
--   Definitions and structural lemmas for Variables Fixed Width Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/VariablesFixedWidthStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
set_option autoImplicit false
section
section
namespace FixedWidth
open Turing MainTheoremForms Groundwork PaddedDescent.F
open Sat3 (CNF)
noncomputable def expVariables (α : ℝ) (n : ℕ) : ℝ := (n : ℝ) * lg (lg n) / lg n ^ α
noncomputable def timeVariables (α : ℝ) (C n : ℕ) : ℕ := ⌊(2 : ℝ) ^ ((C : ℝ) * expVariables α n)⌋₊
def CountsFor (α : ℝ) (k : ℕ) (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), 4 ≤ n → SatK.IsKCNF k φ → CountsWithin M k φ (timeVariables α C n)
def Counts (α : ℝ) : Prop :=
  ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧ ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, CountsFor α k M C
def IsBetween (ρ : ℝ) (x₀ : ℕ) (num : U × U → ℕ × ℕ) : Prop := ∀ l : ℕ,
  0.85 * ρ ^ l ≤ ((num (List.replicate l (), List.replicate (Levels.Gen.K x₀ l) ())).1 : ℝ) / ((num (List.replicate l (), List.replicate (Levels.Gen.K x₀ l) ())).2 : ℝ) ∧
  ((num (List.replicate l (), List.replicate (Levels.Gen.K x₀ l) ())).1 : ℝ) / ((num (List.replicate l (), List.replicate (Levels.Gen.K x₀ l) ())).2 : ℝ) ≤ ρ ^ l
def Proviso (ρ : ℝ) (x₀ : ℕ) : Prop := ∃ num : U × U → ℕ × ℕ, PolyT num ∧ IsBetween ρ x₀ num
def ProvisoHolds : Prop := ∀ x₀ : ℕ, Proviso (11 / 12) x₀ ∧ Proviso (1 / Real.sqrt 2) x₀
def CountsFromPieces : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ), AppRunningTime.Exist ρ c → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → Proviso ρ x₀ → Counts (AppRunningTime.alpha' ρ)
structure RunningTimesFromPieces : Prop where
  /-- (a) -/
  a : ∀ (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 18 ≤ x₀ → AppRunningTime.PartA ρ x₀
  /-- (b); C₀ depends only on c. -/
  b : ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ), AppRunningTime.Exist ρ c → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → AppRunningTime.PartB ρ x₀ C₀
  /-- (c), first sentence: variables need not occur -/
  c_m : ClausesOccur.CountsFromPieces
  /-- (c), second sentence: with the proviso, one machine for all k -/
  c_n : CountsFromPieces
  /-- «as is the case for ρ = 11/12 and for ρ = 1/√2» -/
  c_proviso : ProvisoHolds
  /-- (d), as in `AppRunningTime.ThmRunningTime`. The printed proof of (d) is not formalized; (d)
  follows from a bound of the same form with the larger exponent 3/19 in place of α'/10. -/
  d : ∀ (ρ : ℝ) (c : ℕ), AppRunningTime.Exist ρ c → Sat3.InRateTM (AppRunningTime.alpha' ρ / 10)
end FixedWidth


