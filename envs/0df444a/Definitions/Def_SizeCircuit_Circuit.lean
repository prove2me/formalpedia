-- Prove2me | Definitions.Def_SizeCircuit_Circuit
-- name    : SizeCircuit_Circuit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:47:54.391321+00:00
-- url     : https://prove2.me/theorems/6fc9667a-9c57-4dbf-8a2b-02549bb8ef7d
-- title:
--   Circuit
-- statement:
--   Definitions and structural lemmas for Circuit, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Circuit.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_General
import Definitions.Def_SizeCircuit_Addition
import Definitions.Def_SizeCircuit_Compare
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks ENP
end SizeCircuit


