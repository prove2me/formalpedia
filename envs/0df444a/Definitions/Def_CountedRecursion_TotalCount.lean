-- Prove2me | Definitions.Def_CountedRecursion_TotalCount
-- name    : CountedRecursion_TotalCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:24:16.132438+00:00
-- url     : https://prove2.me/theorems/863b1225-079d-47cb-9def-e4ba15570bfa
-- title:
--   Total Count
-- statement:
--   Definitions and structural lemmas for Total Count, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/TotalCount.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CountBase
import Definitions.Def_CountedRecursion_CountStep
import Definitions.Def_Tower_Cost
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Levels.Gen Printed QueryMachines
end ExplicitCost


