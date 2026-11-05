-- Prove2me | Definitions.Def_Exits_Grouping
-- name    : Exits_Grouping
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:26:37.091186+00:00
-- url     : https://prove2.me/theorems/25c53037-aa0e-4f64-93f3-2cea0a2becee
-- title:
--   Grouping
-- statement:
--   Definitions and structural lemmas for Grouping, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Grouping.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Main
import Definitions.Def_Eight_ViaGrouping_Keeps
import Definitions.Def_ToTuring_Poly_Range
import Mathlib.Tactic.GCongr
set_option autoImplicit false
section
section
@[expose] section
namespace Exits
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset Paper Eight Eight.SecNetworks Eight.ViaGrouping Eight.ViaGrouping.Cost
end Exits


