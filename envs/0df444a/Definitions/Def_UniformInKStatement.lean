-- Prove2me | Definitions.Def_UniformInKStatement
-- name    : UniformInKStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:26:58.954196+00:00
-- url     : https://prove2.me/theorems/3a5847a0-a165-46b8-8e2d-1b2dccea8c1f
-- title:
--   Uniform In KStatement
-- statement:
--   Definitions and structural lemmas for Uniform In KStatement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/UniformInKStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthVariableBoundStatement
set_option autoImplicit false
section
section
namespace SatM
open Turing
open Sat3 (CNF)
def CountsTMN (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ → ℕ) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ →
    Nonempty (TM2OutputsInTime M.tm ((enc k φ).map M.inputAlphabet.invFun)
      (some ((SatK.binary n (SatK.numSat φ)).map M.outputAlphabet.invFun)) (t k n))
noncomputable def boundNK (r : ℕ → ℝ) (C k n : ℕ) : ℕ := ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * (k : ℝ) ^ 2 * n * r n)⌋₊
noncomputable def boundBothK (rn rm : ℕ → ℝ) (C k n m : ℕ) : ℕ :=
  ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * min ((k : ℝ) ^ 2 * n * rn n) ((k : ℝ) * m * rm m))⌋₊
def CountUniformInRate (rn rm : ℕ → ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    CountsTMN M (boundNK rn C) ∧
    CountsTM M (bound rm C) ∧
    ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ → AllOccur φ →
      Nonempty (TM2OutputsInTime M.tm ((enc k φ).map M.inputAlphabet.invFun)
        (some ((SatK.binary n (SatK.numSat φ)).map M.outputAlphabet.invFun)) (boundBothK rn rm C k n φ.length))
def TargetUniform : Prop := CountUniformInRate (SatK.rN 1 (1 / 2)) (rPow (1 / 2))
end SatM


