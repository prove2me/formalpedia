-- Prove2me | Definitions.Def_ClauseBoundStatement
-- name    : ClauseBoundStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:24:53.831969+00:00
-- url     : https://prove2.me/theorems/06bd4212-ba2e-448b-a555-30fcb55a0019
-- title:
--   Clause Bound Statement
-- statement:
--   Definitions and structural lemmas for Clause Bound Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/ClauseBoundStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
set_option autoImplicit false
section
section
namespace SatM
open Turing
open Sat3 (CNF)
def AllOccur {n : ℕ} (φ : CNF n) : Prop := ∀ i : Fin n, ∃ C ∈ φ, ∃ l ∈ C, l.1 = i
def enc (k : ℕ) {n : ℕ} (φ : CNF n) : List Bool := List.replicate k true ++ false :: SatK.enc k φ
def CountsTM (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ → ℕ) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → AllOccur φ →
    Nonempty (TM2OutputsInTime M.tm ((enc k φ).map M.inputAlphabet.invFun)
      (some ((SatK.binary n (SatK.numSat φ)).map M.outputAlphabet.invFun)) (t k φ.length))
noncomputable def bound (r : ℕ → ℝ) (C k m : ℕ) : ℕ := ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * k * m * r m)⌋₊
def CountInRate (r : ℕ → ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ CountsTM M (bound r C)
noncomputable def rPow (α : ℝ) (m : ℕ) : ℝ := 1 / Real.logb 2 ((m : ℝ) + 2) ^ α
def TargetSqrt : Prop := CountInRate (rPow (1 / 2))
end SatM


