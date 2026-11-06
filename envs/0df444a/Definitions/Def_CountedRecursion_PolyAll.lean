-- Prove2me | Definitions.Def_CountedRecursion_PolyAll
-- name    : CountedRecursion_PolyAll
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:53:52.691376+00:00
-- url     : https://prove2.me/theorems/3e15dddb-4576-4688-848d-4c13aa07b1ee
-- title:
--   Poly All
-- statement:
--   Definitions and structural lemmas for Poly All, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyAll.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolyEnd
import Definitions.Def_ExplicitCost_GroupingPoly
import Definitions.Def_Tower_PolyTower
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Groundwork QueryMachines Printed
end ExplicitCost


