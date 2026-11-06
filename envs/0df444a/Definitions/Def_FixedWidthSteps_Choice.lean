-- Prove2me | Definitions.Def_FixedWidthSteps_Choice
-- name    : FixedWidthSteps_Choice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:23:57.190607+00:00
-- url     : https://prove2.me/theorems/b068c18b-3e28-42e9-a0b0-01ed5b334de6
-- title:
--   Choice
-- statement:
--   Definitions and structural lemmas for Choice, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Choice.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_Absorb
import Definitions.Def_UniformInK_Top_Time
set_option autoImplicit false
section
section
@[expose] section
namespace FixedWidthSteps
open Turing Groundwork ClauseBound.Alg MainTheoremForms TwoMachines PairsToBound FixedWidth Wrap
end FixedWidthSteps


