-- Prove2me | Definitions.Def_SplitCount_Leaf
-- name    : SplitCount_Leaf
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:39:54.356199+00:00
-- url     : https://prove2.me/theorems/3128ebe8-1577-40f5-be4b-22595d98711b
-- title:
--   Leaf
-- statement:
--   Definitions and structural lemmas for Leaf, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Leaf.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Width
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
section
section
@[expose] section
namespace SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight.Width Occ
def leafConst (k Bl : ℕ) : ℕ :=
  (1 + (max k 3 - 3) * Bl) + (1 + 3 * (max k 3 - 3)) * Bl * (3 * (1 + (max k 3 - 3) * Bl) + 11) + 2
def stackConst (k Dd Sk : ℕ) : ℕ := (Dd + 1) * (4 * (Sk * (4 * max k 2 + 2)) + 6) + 1
end SplitCount


