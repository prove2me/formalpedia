-- Prove2me | Definitions.Def_StepMachines_Prog_SidePresents
-- name    : StepMachines_Prog_SidePresents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:09:26.864938+00:00
-- url     : https://prove2.me/theorems/86dc80cf-fc5b-456a-b142-8f74b0e7429b
-- title:
--   Side Presents
-- statement:
--   Definitions and structural lemmas for Side Presents, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/SidePresents.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Side
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridCount
set_option autoImplicit false
section
section
namespace Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 sideN sideCap)
def sideA (g : ℕ) : ℕ := 4 * g ^ 4 + 8 * g ^ 3 + 20 * g ^ 2 + 20 * g + 1000
end Groundwork.Prog


