-- Prove2me | Definitions.Def_ClausesOccurStatement
-- name    : ClausesOccurStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:45:31.798195+00:00
-- url     : https://prove2.me/theorems/f4aac591-38b1-4a73-b40a-4163703ad6da
-- title:
--   Clauses Occur Statement
-- statement:
--   Definitions and structural lemmas for Clauses Occur Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/ClausesOccurStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_AppRunningTimeStatement
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace ClausesOccur
open Turing MainTheoremForms
open Sat3 (CNF)
noncomputable def expClauses (α : ℝ) (k m : ℕ) : ℝ := (k : ℝ) * m / lg m ^ α
noncomputable def timeClauses (α : ℝ) (C k m : ℕ) : ℕ := ⌊(2 : ℝ) ^ ((C : ℝ) * expClauses α k m)⌋₊
def ExpHalfStmt : Prop := ∀ k m : ℕ, expClauses (1 / 2) k m = expM k m
def CountsFor (α : ℝ) (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length →
    CountsOccWithinC M k φ (timeClauses α C k φ.length + C * (encC k φ).length ^ C)
def Counts (α : ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ CountsFor α M C
def CountsUnaryFor (α : ℝ) (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length →
    CountsOccWithin M k φ (timeClauses α C k φ.length + C * (SatM.enc k φ).length ^ C)
def CountsUnary (α : ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ CountsUnaryFor α M C
def AllOccurOfUnaryStmt : Prop := ∀ α : ℝ, 0 ≤ α → α ≤ 1 → ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), CountsUnaryFor α M C →
  ∃ C' : ℕ, ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 2 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ → CountsWithin M k φ (SatM.bound (SatM.rPow α) C' k φ.length)
def SomeVariableOccursStmt : Prop := ∀ (N : ℕ) (φ : CNF N), φ.Nodup → 2 ≤ φ.length → 1 ≤ numOcc φ
def CountsFromPieces : Prop := ∀ (ρ : ℝ) (c : ℕ), AppRunningTime.Exist ρ c → Counts (AppRunningTime.alpha' ρ)
def CountsUnaryFromPieces : Prop := ∀ (ρ : ℝ) (c : ℕ), AppRunningTime.Exist ρ c → CountsUnary (AppRunningTime.alpha' ρ)
def BoundInClausesFor (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length →
    CountsOccWithinC M k φ (⌊(2 : ℝ) ^ ((C : ℝ) * expM k φ.length)⌋₊ + C * (encC k φ).length ^ C)
def BoundInClauses : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ BoundInClausesFor M C
def BoundInClausesIsHalfStmt : Prop := ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), BoundInClausesFor M C ↔ CountsFor (1 / 2) M C
def BoundInClausesFromStmt : Prop := AppRunningTime.ThmHalfPieces → CountsFromPieces → BoundInClauses
structure RunningTimesFromPieces : Prop where
  /-- (a) -/
  a : ∀ (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 18 ≤ x₀ → AppRunningTime.PartA ρ x₀
  /-- (b); C₀ depends only on c. -/
  b : ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ), AppRunningTime.Exist ρ c → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → AppRunningTime.PartB ρ x₀ C₀
  /-- (c), first sentence, with a term polynomial in the length of the input added to the bound -/
  c_m : CountsFromPieces
  /-- (c), second sentence, as in `AppRunningTime.ThmRunningTime`: for every fixed k. The printed
  proviso (a number between 0.85ρ^ℓ and ρ^ℓ can be computed from ℓ in time polynomial in K_ℓ) is not
  needed by the proof in this development and is not made. -/
  c_n : ∀ (ρ : ℝ) (c : ℕ), AppRunningTime.Exist ρ c → ∀ k : ℕ, 1 ≤ k → SatK.CountInRateN k (SatK.rN 1 (AppRunningTime.alpha' ρ))
  /-- (d), as in `AppRunningTime.ThmRunningTime`. In this development it follows from the 3-SAT
  bound `Sat3.InRateTM` with the exponent 3/19 of log n in place of α'/10, which is the stronger
  bound, as α'/10 ≤ 1/10 < 3/19 (α' ≤ 1 since ρ ≥ ½); the printed proof of (d) is not formalized. -/
  d : ∀ (ρ : ℝ) (c : ℕ), AppRunningTime.Exist ρ c → Sat3.InRateTM (AppRunningTime.alpha' ρ / 10)
end ClausesOccur


