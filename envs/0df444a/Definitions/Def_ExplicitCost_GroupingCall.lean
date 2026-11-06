-- Prove2me | Definitions.Def_ExplicitCost_GroupingCall
-- name    : ExplicitCost_GroupingCall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:26:29.626188+00:00
-- url     : https://prove2.me/theorems/68518b81-75e0-4080-92b9-4a23521d0e36
-- title:
--   Grouping Call
-- statement:
--   Definitions and structural lemmas for Grouping Call, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingCall.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingSearch
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Value_End
import Definitions.Def_GeneralPieces_Main
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace Sizes
end Sizes
open Sizes
end ExplicitCost


