-- Prove2me | Definitions.Def_SplitCount_StepOne
-- name    : SplitCount_StepOne
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:43:39.88934+00:00
-- url     : https://prove2.me/theorems/e8416875-74ac-4ce1-b326-deae2fc688dd
-- title:
--   Step One
-- statement:
--   Definitions and structural lemmas for Step One, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/StepOne.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_Occ_Main
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_Alg
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
set_option autoImplicit false
section
section
@[expose] section
namespace SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
end SplitCount


