-- Prove2me | Definitions.Def_SizeCircuit_Gamma
-- name    : SizeCircuit_Gamma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:37:37.365148+00:00
-- url     : https://prove2.me/theorems/49a216ac-803c-4e5e-bb0f-6918c5b8224c
-- title:
--   Gamma
-- statement:
--   Definitions and structural lemmas for Gamma, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Gamma.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_SizeCircuit_General
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound CircuitLowerBound.Blocks ENP
end SizeCircuit


