-- Prove2me | Definitions.Def_Exits_Count
-- name    : Exits_Count
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:32:50.413909+00:00
-- url     : https://prove2.me/theorems/406f6061-c1b0-41c4-be01-20ec463a7481
-- title:
--   Count
-- statement:
--   Definitions and structural lemmas for Count, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Count.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Exits_Level
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic.Positivity
set_option autoImplicit false
section
section
@[expose] section
namespace Exits
open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping
end Exits


