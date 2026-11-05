-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_Approx
-- name    : ClauseBound_ParityChecks_Approx
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:17:18.037094+00:00
-- url     : https://prove2.me/theorems/e2c96694-f80d-4d62-b592-7297ad0a9784
-- title:
--   Approx
-- statement:
--   Definitions and structural lemmas for Approx, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks.Approx
open Finset _root_.ParityChecks
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
end ClauseBound.ParityChecks.Approx


