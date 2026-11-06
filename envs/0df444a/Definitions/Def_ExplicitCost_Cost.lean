-- Prove2me | Definitions.Def_ExplicitCost_Cost
-- name    : ExplicitCost_Cost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:00:57.200183+00:00
-- url     : https://prove2.me/theorems/fd2c5731-d736-48d0-803b-b91cbd5be6df
-- title:
--   Cost
-- statement:
--   Definitions and structural lemmas for Cost, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Cost.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_SameRuns
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_QueryMachines_Runs
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


