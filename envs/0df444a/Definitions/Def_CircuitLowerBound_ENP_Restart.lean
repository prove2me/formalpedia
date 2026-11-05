-- Prove2me | Definitions.Def_CircuitLowerBound_ENP_Restart
-- name    : CircuitLowerBound_ENP_Restart
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:12:57.648727+00:00
-- url     : https://prove2.me/theorems/8aaa3b9d-e38d-428a-9be1-dcb4e548c23c
-- title:
--   Restart
-- statement:
--   Definitions and structural lemmas for Restart, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Restart.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_ENP_Round
import Definitions.Def_CircuitLowerBound_Small
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace CircuitLowerBound
open ENP Groundwork PaddedDescent Turing
namespace Restart
end Restart
open Restart
end CircuitLowerBound


