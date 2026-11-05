-- Prove2me | Definitions.Def_Suffices_Sizes
-- name    : Suffices_Sizes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:19:37.736697+00:00
-- url     : https://prove2.me/theorems/0d02d36f-4fb0-4275-82c7-03723fe056f3
-- title:
--   Sizes
-- statement:
--   Definitions and structural lemmas for Sizes, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Defs
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Tactic.Ring
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace Suffices
open Groundwork Groundwork.Prog CountKSat Exits
end Suffices


