-- Prove2me | Definitions.Def_Eight_ViaGrouping_Level
-- name    : Eight_ViaGrouping_Level
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:45:41.445865+00:00
-- url     : https://prove2.me/theorems/6f3cf3c7-03fc-4cae-b27b-9b8846199281
-- title:
--   Level
-- statement:
--   Definitions and structural lemmas for Level, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Level.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelNet
import Definitions.Def_Eight_Level_Arith
import Definitions.Def_Eight_Level_Min
import Definitions.Def_StepMachines_Prog_GridLoop
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level
end Eight.ViaGrouping


