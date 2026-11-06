-- Prove2me | Definitions.Def_CountedRecursion_TotalRoom
-- name    : CountedRecursion_TotalRoom
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:15:10.556025+00:00
-- url     : https://prove2.me/theorems/3a33eaad-d8be-45b7-9980-f693dcd72521
-- title:
--   Total Room
-- statement:
--   Definitions and structural lemmas for Total Room, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/TotalRoom.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Levels.Gen Printed QueryMachines Finset
end ExplicitCost


