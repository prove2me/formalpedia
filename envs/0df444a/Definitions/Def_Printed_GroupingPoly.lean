-- Prove2me | Definitions.Def_Printed_GroupingPoly
-- name    : Printed_GroupingPoly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:35:34.347697+00:00
-- url     : https://prove2.me/theorems/c313fc1a-f811-4dbb-82e3-b629881bc76b
-- title:
--   Grouping Poly
-- statement:
--   Definitions and structural lemmas for Grouping Poly, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingPoly.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_Eight_ViaGrouping_Keeps
import Definitions.Def_Exits_Poly
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Printed
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
end Printed


