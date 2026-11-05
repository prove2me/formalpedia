-- Prove2me | Definitions.Def_Exits_Decides
-- name    : Exits_Decides
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:25:24.614029+00:00
-- url     : https://prove2.me/theorems/5221d0db-6f39-430f-ba91-c970ad8f83c4
-- title:
--   Decides
-- statement:
--   Definitions and structural lemmas for Decides, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Decides.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_SecLevel_EStar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
section
section
@[expose] section
namespace Exits
open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping Suffices Enumerate
end Exits


