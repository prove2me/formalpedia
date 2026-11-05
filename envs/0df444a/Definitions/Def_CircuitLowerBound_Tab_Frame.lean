-- Prove2me | Definitions.Def_CircuitLowerBound_Tab_Frame
-- name    : CircuitLowerBound_Tab_Frame
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:55:00.568572+00:00
-- url     : https://prove2.me/theorems/932f632b-cb56-4506-9f2c-d9b23d5c39c2
-- title:
--   Frame
-- statement:
--   Definitions and structural lemmas for Frame, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
set_option autoImplicit false
section
section
namespace CircuitLowerBound.Tab
open ENP Turing
section generic
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
end generic
variable (N : TM2ComputableAux Bool Bool)
def caseOf (c : N.tm.Cfg) : Case N := (c.l, c.var, fun k j => (c.stk k)[j.val]?)
def stay (c : N.tm.Cfg) : N.tm.Cfg := (N.tm.step c).getD c
end CircuitLowerBound.Tab


