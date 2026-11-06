-- Prove2me | Definitions.Def_CountedInstance_Main
-- name    : CountedInstance_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:35:26.093037+00:00
-- url     : https://prove2.me/theorems/14ddc38b-54ca-4a46-bf88-b688680ed210
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/CountedInstance/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedInstanceStatement
import Definitions.Def_CountedInstance_Pairs
import Definitions.Def_CountedToPadded_GenLevels
import Definitions.Def_PiecesCounted_Half
import Definitions.Def_PiecesCounted_Assume
import Definitions.Def_CountedRecursion_Main
set_option autoImplicit false
section
section
@[expose] section
namespace CountedInstance
open Groundwork QueryMachines Printed ExplicitCost
end CountedInstance


