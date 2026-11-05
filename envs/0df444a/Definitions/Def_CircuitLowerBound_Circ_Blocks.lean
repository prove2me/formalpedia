-- Prove2me | Definitions.Def_CircuitLowerBound_Circ_Blocks
-- name    : CircuitLowerBound_Circ_Blocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:55:14.932423+00:00
-- url     : https://prove2.me/theorems/54f44506-b9a8-4777-98d7-1e51ab93f96e
-- title:
--   Blocks
-- statement:
--   Definitions and structural lemmas for Blocks, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
set_option autoImplicit false
section
section
namespace CircuitLowerBound.Blocks
open ENP Groundwork
abbrev B4 : Type := Bool × Bool × Bool × Bool
def opZero : B4 := (false, false, false, false)
def opOne : B4 := (true, true, true, true)
def opAnd : B4 := (false, false, false, true)
def opOr : B4 := (false, true, true, true)
def opXor : B4 := (false, true, true, false)
def opFst : B4 := (false, false, true, true)
def opAndN : B4 := (false, false, true, false)
def gval (v : ℕ → Bool) (g : GateD) : Bool := g.toGate.op (v g.2.1) (v g.2.2)
def Obeys (v : ℕ → Bool) : ℕ → List GateD → Prop
  | _, [] => True
  | n, g :: C => v n = gval v g ∧ Obeys v (n + 1) C
def WFa : ℕ → List GateD → Prop
  | _, [] => True
  | n, g :: C => (g.2.1 < n ∧ g.2.2 < n) ∧ WFa (n + 1) C
def prevW (off init i : ℕ) : ℕ := if i = 0 then init else off + i - 1
def num (b : ℕ → Bool) (w : ℕ) : ℕ := ofWord ((List.range w).map b)
end CircuitLowerBound.Blocks


