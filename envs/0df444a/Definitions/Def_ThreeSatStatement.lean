-- Prove2me | Definitions.Def_ThreeSatStatement
-- name    : ThreeSatStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:12.532739+00:00
-- url     : https://prove2.me/theorems/ea616de6-2dff-4885-89b4-2307a77b1fa1
-- title:
--   Three Sat Statement
-- statement:
--   Definitions and structural lemmas for Three Sat Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/ThreeSatStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Computability.TuringMachine.Computable
set_option autoImplicit false
section
section
namespace Sat3
open Turing
open scoped NNReal ENNReal
abbrev Lit (n : ℕ) : Type := Fin n × Bool
abbrev CNF (n : ℕ) : Type := List (List (Lit n))
def Satisfiable {n : ℕ} (φ : CNF n) : Prop := ∃ a : Fin n → Bool, ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2
def Is3CNF {n : ℕ} (φ : CNF n) : Prop := (∀ C ∈ φ, C.length ≤ 3) ∧ φ.Nodup
def slot {n : ℕ} : Option (Lit n) → ℕ
  | none => 0
  | some l => 2 * l.1.val + 1 + l.2.toNat
def enc {n : ℕ} (φ : CNF n) : List Bool :=
  List.replicate n true ++ false :: φ.flatMap fun C => (List.range 3).flatMap fun j =>
    (List.range (Nat.log2 (2 * n) + 1)).map (slot C[j]?).testBit
def DecidesTM (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), Is3CNF φ → ∃ b : Bool, (b = true ↔ Satisfiable φ) ∧
    Nonempty (TM2OutputsInTime M.tm ((enc φ).map M.inputAlphabet.invFun)
      (some ([b].map M.outputAlphabet.invFun)) (t n))
def InTimeTM (δ : ℝ≥0) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
    DecidesTM M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊
noncomputable def s₃TM : ℝ≥0∞ := ⨅ (δ : ℝ≥0) (_ : InTimeTM δ), (δ : ℝ≥0∞)
def ETH_TM : Prop := 0 < s₃TM
end Sat3


