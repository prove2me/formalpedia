-- Prove2me | Definitions.Def_ExplicitCost_GroupingLemma
-- name    : ExplicitCost_GroupingLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:31:42.615997+00:00
-- url     : https://prove2.me/theorems/e648c84b-c317-4240-adb1-9030ecb49c3e
-- title:
--   Grouping Lemma
-- statement:
--   Definitions and structural lemmas for Grouping Lemma, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingLemma.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingNumbers
import Definitions.Def_ExplicitCost_GroupingSearch
import Definitions.Def_ExplicitCost_GroupingCall
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_Printed_Achievable
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_GeneralPieces_Main
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed Sizes
@[expose] def groupW {g K : ℕ} (N : Net g) (P B : ℕ) (hK0 : 0 < K) (x L : ℕ) : ℕ → List Bool → ℤ :=
  fun w z => if h : w < K then (Value.groupClique asked.under (netInput N P B) N hK0 x L).W ⟨w, h⟩ z else 0
end ExplicitCost


