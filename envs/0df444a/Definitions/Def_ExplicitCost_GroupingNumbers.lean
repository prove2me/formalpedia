-- Prove2me | Definitions.Def_ExplicitCost_GroupingNumbers
-- name    : ExplicitCost_GroupingNumbers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:02:13.100008+00:00
-- url     : https://prove2.me/theorems/77fb9f8a-9370-4463-88b9-ef2252e5b68a
-- title:
--   Grouping Numbers
-- statement:
--   Definitions and structural lemmas for Grouping Numbers, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingNumbers.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Eight_ViaGrouping_Search
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ)
variable {P B}
end ExplicitCost


