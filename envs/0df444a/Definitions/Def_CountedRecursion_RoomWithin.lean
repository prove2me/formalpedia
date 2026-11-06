-- Prove2me | Definitions.Def_CountedRecursion_RoomWithin
-- name    : CountedRecursion_RoomWithin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:19:12.284525+00:00
-- url     : https://prove2.me/theorems/9fac0156-d501-463d-a0d1-506aa529a539
-- title:
--   Room Within
-- statement:
--   Definitions and structural lemmas for Room Within, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RoomWithin.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Levels.Gen Printed Finset
end ExplicitCost


