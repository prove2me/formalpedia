-- Prove2me | Definitions.Def_Printed_GroupingRun
-- name    : Printed_GroupingRun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:02:26.034504+00:00
-- url     : https://prove2.me/theorems/51ef75fd-c6c7-4f66-af20-1bb558e12ee8
-- title:
--   Grouping Run
-- statement:
--   Definitions and structural lemmas for Grouping Run, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Eight_ViaGrouping_Main
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
@[expose] def groupTables {g K : ℕ} (N : Net g) (P B : ℕ) (hK0 : 0 < K) (x L : ℕ) : ℕ → List Bool → ℤ :=
  fun w z => if h : w < K then (Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x L).W ⟨w, h⟩ z else 0
end Printed


