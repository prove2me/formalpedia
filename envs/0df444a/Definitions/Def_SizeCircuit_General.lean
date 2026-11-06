-- Prove2me | Definitions.Def_SizeCircuit_General
-- name    : SizeCircuit_General
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:31:17.181192+00:00
-- url     : https://prove2.me/theorems/9f4d3250-7bfe-41b5-8970-b2ca7de6f8f5
-- title:
--   General
-- statement:
--   Definitions and structural lemmas for General, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_CircuitLowerBound_Circ_Form
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace SizeCircuit
open Groundwork Groundwork.Prog CountKSat CircuitLowerBound CircuitLowerBound.Blocks ENP
@[expose] def wireVal (x : List Bool) (K : List GateD) (i : ℕ) : Bool := (wires x (toC K)).getD i false
end SizeCircuit


