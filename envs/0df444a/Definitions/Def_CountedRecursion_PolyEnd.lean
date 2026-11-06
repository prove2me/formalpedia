-- Prove2me | Definitions.Def_CountedRecursion_PolyEnd
-- name    : CountedRecursion_PolyEnd
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:45:42.047394+00:00
-- url     : https://prove2.me/theorems/d2a6497a-e6e6-465d-afa6-4a8135270c06
-- title:
--   Poly End
-- statement:
--   Definitions and structural lemmas for Poly End, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyEnd.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_PolyProcedure
import Definitions.Def_CountedRecursion_PolySolver
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Groundwork QueryMachines Printed
end ExplicitCost


