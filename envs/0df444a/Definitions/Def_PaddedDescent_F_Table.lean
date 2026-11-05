-- Prove2me | Definitions.Def_PaddedDescent_F_Table
-- name    : PaddedDescent_F_Table
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:09:15.665381+00:00
-- url     : https://prove2.me/theorems/34d57e0a-0a73-49c7-8859-7a647e486091
-- title:
--   Table
-- statement:
--   Definitions and structural lemmas for Table, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Table.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridDefs
set_option autoImplicit false
section
section
@[expose] section
namespace PaddedDescent.F.Table
open Groundwork Groundwork.Prog Finset
def skip (v j : ℕ) : ℕ := if j < v then j else j + 1
end PaddedDescent.F.Table


