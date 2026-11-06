-- Prove2me | Definitions.Def_Printed_LevelCost
-- name    : Printed_LevelCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:02:41.366886+00:00
-- url     : https://prove2.me/theorems/0036b069-cde6-411a-91d1-fc424a1e81a5
-- title:
--   Level Cost
-- statement:
--   Definitions and structural lemmas for Level Cost, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelCost.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelNetworks
import Definitions.Def_Eight_ViaGrouping_Level
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
end Printed


