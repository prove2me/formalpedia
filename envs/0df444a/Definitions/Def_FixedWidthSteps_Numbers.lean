-- Prove2me | Definitions.Def_FixedWidthSteps_Numbers
-- name    : FixedWidthSteps_Numbers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:11:24.782145+00:00
-- url     : https://prove2.me/theorems/821a9dce-7b1a-47bc-b67d-95f812e343ca
-- title:
--   Numbers
-- statement:
--   Definitions and structural lemmas for Numbers, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Numbers.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_RouteDefs
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Between
import Definitions.Def_GeneralPieces_Num_Remarks
set_option autoImplicit false
section
section
@[expose] section
namespace FixedWidthSteps
open Groundwork PaddedDescent.F Levels.Gen MainTheoremForms FixedWidth
end FixedWidthSteps
namespace FixedWidth
open Groundwork PaddedDescent.F
end FixedWidth


