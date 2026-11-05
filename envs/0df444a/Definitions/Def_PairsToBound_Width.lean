-- Prove2me | Definitions.Def_PairsToBound_Width
-- name    : PairsToBound_Width
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:44:35.528234+00:00
-- url     : https://prove2.me/theorems/8a066049-e68f-4be9-9f0f-d83b2eacb0c4
-- title:
--   Width
-- statement:
--   Definitions and structural lemmas for Width, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Width.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Mathlib.Tactic.Ring
set_option autoImplicit false
section
section
@[expose] section
namespace PairsToBound
open Sat3 (CNF)
end PairsToBound


