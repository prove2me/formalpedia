-- Prove2me | Definitions.Def_CountKSatStatement
-- name    : CountKSatStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:23:27.254826+00:00
-- url     : https://prove2.me/theorems/f6785bc3-9b42-40b6-a3f4-648946191e66
-- title:
--   Count KSat Statement
-- statement:
--   Definitions and structural lemmas for Count KSat Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/CountKSatStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
import Mathlib.Data.Fintype.Pi
set_option autoImplicit false
section
section
namespace SatK
open Turing
open Sat3 (CNF)
open scoped NNReal ENNReal
def numSat {n : ℕ} (φ : CNF n) : ℕ := (Finset.univ.filter fun a : Fin n → Bool => ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2).card
def binary (n N : ℕ) : List Bool := (List.range (n + 1)).map N.testBit
def CountsTM (k : ℕ) (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), IsKCNF k φ →
    Nonempty (TM2OutputsInTime M.tm ((enc k φ).map M.inputAlphabet.invFun)
      (some ((binary n (numSat φ)).map M.outputAlphabet.invFun)) (t n))
def CountInTimeTM (k : ℕ) (δ : ℝ≥0) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    CountsTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊
def CountETH_TM : Prop := ∃ δ : ℝ≥0, 0 < δ ∧ ¬ CountInTimeTM 3 δ
end SatK


