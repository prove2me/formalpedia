-- Prove2me | Definitions.Def_CircuitLowerBound_Oracle_Restart
-- name    : CircuitLowerBound_Oracle_Restart
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T18:01:49.964716+00:00
-- url     : https://prove2.me/theorems/38766c7d-3ccf-4aa0-8fd9-db0c08fcab2a
-- title:
--   Restart
-- statement:
--   Definitions and structural lemmas for Restart, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Runs
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace CircuitLowerBound
open ENP Turing Groundwork.TM
namespace Oracle
variable {M : TM2ComputableAux Bool Bool}
end Oracle
end CircuitLowerBound


