-- Prove2me | Definitions.Def_SplitCount_Suffices
-- name    : SplitCount_Suffices
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:45:11.882392+00:00
-- url     : https://prove2.me/theorems/c1d5df3d-8f69-439d-bc82-81f5d83edf38
-- title:
--   Suffices
-- statement:
--   Definitions and structural lemmas for Suffices, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Suffices.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Leaf
import Definitions.Def_CountKSat_Walk
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
section
section
@[expose] section
namespace SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify Paper CountKSat Eight Eight.Width Occ
end SplitCount


