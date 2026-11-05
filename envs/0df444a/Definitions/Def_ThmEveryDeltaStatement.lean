-- Prove2me | Definitions.Def_ThmEveryDeltaStatement
-- name    : ThmEveryDeltaStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:21:09.506204+00:00
-- url     : https://prove2.me/theorems/eb8355f0-89cf-4e5f-8f49-8acf29a8b20d
-- title:
--   Thm Every Delta Statement
-- statement:
--   Definitions and structural lemmas for Thm Every Delta Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/ThmEveryDeltaStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
set_option autoImplicit false
section
section
namespace Sat3
open Turing
def HaltsWith (M : TM2ComputableAux Bool Bool) {n : ℕ} (φ : CNF n) (b : Bool) (t : ℕ) : Prop :=
  Nonempty (TM2OutputsInTime M.tm ((enc φ).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)
def DecidedInTime (δ : ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
    ∀ (n : ℕ) (φ : CNF n), Is3CNF φ → ∃ (b : Bool) (t : ℕ),
      (b = true ↔ Satisfiable φ) ∧ (t : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) ∧ HaltsWith M φ b t
def ThmEveryDelta : Prop := ∀ δ : ℝ, 0 < δ → DecidedInTime δ
end Sat3


