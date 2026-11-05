-- Prove2me | Definitions.Def_KSatStatement
-- name    : KSatStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:19.026203+00:00
-- url     : https://prove2.me/theorems/7233d491-8332-49c5-9d77-51fb187fbffe
-- title:
--   KSat Statement
-- statement:
--   Definitions and structural lemmas for KSat Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/KSatStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
set_option autoImplicit false
section
section
namespace SatK
open Turing
open Sat3 (Lit CNF Satisfiable slot)
open scoped NNReal ENNReal
def IsKCNF (k : ℕ) {n : ℕ} (φ : CNF n) : Prop := (∀ C ∈ φ, C.length ≤ k) ∧ φ.Nodup
def enc (k : ℕ) {n : ℕ} (φ : CNF n) : List Bool :=
  List.replicate n true ++ false :: φ.flatMap fun C => (List.range k).flatMap fun j =>
    (List.range (Nat.log2 (2 * n) + 1)).map (slot C[j]?).testBit
def DecidesTM (k : ℕ) (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), IsKCNF k φ → ∃ b : Bool, (b = true ↔ Satisfiable φ) ∧
    Nonempty (TM2OutputsInTime M.tm ((enc k φ).map M.inputAlphabet.invFun)
      (some ([b].map M.outputAlphabet.invFun)) (t n))
def InTimeTM (k : ℕ) (δ : ℝ≥0) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    DecidesTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊
noncomputable def sTM (k : ℕ) : ℝ≥0∞ := ⨅ (δ : ℝ≥0) (_ : InTimeTM k δ), (δ : ℝ≥0∞)
end SatK


