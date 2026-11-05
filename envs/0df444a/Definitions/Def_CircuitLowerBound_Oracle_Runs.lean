-- Prove2me | Definitions.Def_CircuitLowerBound_Oracle_Runs
-- name    : CircuitLowerBound_Oracle_Runs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:57:37.128748+00:00
-- url     : https://prove2.me/theorems/1830b963-94cc-4100-9c93-ca1f5ded50c6
-- title:
--   Runs
-- statement:
--   Definitions and structural lemmas for Runs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Machine
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable {M : TM2ComputableAux Bool Bool} (O : Lang)
def pushed (M : TM2ComputableAux Bool Bool) (mark : Bool) : List Bool → List (M.tm.Γ M.tm.k₀) → List (M.tm.Γ M.tm.k₀)
  | [], L => L
  | b :: l, L => pushed M mark l (if mark then M.inputAlphabet.invFun true :: M.inputAlphabet.invFun b :: L else M.inputAlphabet.invFun b :: L)
end CircuitLowerBound.Oracle


