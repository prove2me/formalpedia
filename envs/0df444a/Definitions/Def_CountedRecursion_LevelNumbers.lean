-- Prove2me | Definitions.Def_CountedRecursion_LevelNumbers
-- name    : CountedRecursion_LevelNumbers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:58:32.399194+00:00
-- url     : https://prove2.me/theorems/9f5f403f-354d-4e1c-8955-41a9dc74b68f
-- title:
--   Level Numbers
-- statement:
--   Definitions and structural lemmas for Level Numbers, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Numbers
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Levels.Gen
end ExplicitCost


