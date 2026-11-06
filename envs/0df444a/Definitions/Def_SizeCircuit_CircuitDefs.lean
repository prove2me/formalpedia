-- Prove2me | Definitions.Def_SizeCircuit_CircuitDefs
-- name    : SizeCircuit_CircuitDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:35:20.266856+00:00
-- url     : https://prove2.me/theorems/40ddd2df-5a26-46c8-81dc-40d5228ff143
-- title:
--   Circuit Defs
-- statement:
--   Definitions and structural lemmas for Circuit Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/CircuitDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
namespace SizeCircuit
open CircuitLowerBound CircuitLowerBound.Blocks
def fullAdder (N a u v : ℕ) : List GateD :=
  [(opXor, a, u), (opXor, N, v), (opAnd, a, u), (opAnd, N, v), (opOr, N + 2, N + 3)]
def halfAdder (a u : ℕ) : List GateD := [(opXor, a, u), (opAnd, a, u)]
abbrev AddState : Type := List ℕ × List ℕ × List ℕ × List GateD
def addStep (n : ℕ) (st : AddState) : AddState :=
  match st.1 with
  | a :: u :: v :: r => ((n + st.2.2.2.length + 1) :: r, (n + st.2.2.2.length + 4) :: st.2.1, st.2.2.1, st.2.2.2 ++ fullAdder (n + st.2.2.2.length) a u v)
  | [a, u] => ((n + st.2.2.2.length + 1) :: st.2.1, [], st.2.2.1 ++ [n + st.2.2.2.length], st.2.2.2 ++ halfAdder a u)
  | [a] => (st.2.1, [], st.2.2.1 ++ [a], st.2.2.2)
  | [] => st
def addStart (n : ℕ) : AddState := (List.range n, [], [], [])
def added (n : ℕ) : AddState := (addStep n)^[n] (addStart n)
def compareGates (N s : ℕ) (digits : List ℕ) : List GateD :=
  ((if s < 2 ^ digits.length then opOne else opZero), 0, 0) ::
    (List.range digits.length).map fun i => ((if s.testBit i then opAnd else opAndN), N + i, digits.getD i 0)
def sizeGates (n s : ℕ) : List GateD :=
  (added n).2.2.2 ++ compareGates (n + (added n).2.2.2.length) s (added n).2.2.1
def StSizeGates : Prop := ∃ a : ℕ, TestsSize sizeGates a ∧ CertGates sizeGates
end SizeCircuit


