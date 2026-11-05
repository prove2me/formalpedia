-- Prove2me | Definitions.Def_Eight_ViaGrouping_LevelNet
-- name    : Eight_ViaGrouping_LevelNet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:00:09.517204+00:00
-- url     : https://prove2.me/theorems/c61bd742-9cf7-4b57-a74b-2cfa047977fa
-- title:
--   Level Net
-- statement:
--   Definitions and structural lemmas for Level Net, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_StepMachines_Prog_GridDefs
import Mathlib.Tactic
set_option autoImplicit false
section
section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level
def lvlPsiSize (g : ℕ) : ℕ := 2 * nRect g + 2 * size g + 4 * g ^ 3 + g + g ^ 2 + 10
end Eight.ViaGrouping


