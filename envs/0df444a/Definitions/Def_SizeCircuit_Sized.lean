-- Prove2me | Definitions.Def_SizeCircuit_Sized
-- name    : SizeCircuit_Sized
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:44:07.257468+00:00
-- url     : https://prove2.me/theorems/26c7deab-9770-4d1d-8ac7-fea447af5874
-- title:
--   Sized
-- statement:
--   Definitions and structural lemmas for Sized, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Sized.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_SizeCircuit_Gamma
import Definitions.Def_GraphProblems_Sized
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight
end SizeCircuit


