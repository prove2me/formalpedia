-- Prove2me | Definitions.Def_FixedWidthVariableBoundStatement
-- name    : FixedWidthVariableBoundStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:26:25.234943+00:00
-- url     : https://prove2.me/theorems/f9143abf-04dc-4a23-8f23-913c1307212b
-- title:
--   Fixed Width Variable Bound Statement
-- statement:
--   Definitions and structural lemmas for Fixed Width Variable Bound Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/FixedWidthVariableBoundStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBoundStatement
set_option autoImplicit false
section
section
namespace SatK
open Turing
noncomputable def boundN (r : ℕ → ℝ) (C n : ℕ) : ℕ := ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * n * r n)⌋₊
def CountInRateN (k : ℕ) (r : ℕ → ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ CountsTM k M (boundN r C)
noncomputable def rN (j : ℕ) (α : ℝ) (n : ℕ) : ℝ := Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) ^ j / Real.logb 2 ((n : ℝ) + 4) ^ α
end SatK


