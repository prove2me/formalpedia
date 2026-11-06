-- Prove2me | Definitions.Def_SplitSat_Walk
-- name    : SplitSat_Walk
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:41:44.605329+00:00
-- url     : https://prove2.me/theorems/8c0c790a-8482-48b8-bb5a-d57aa2bc3ecd
-- title:
--   Walk
-- statement:
--   Definitions and structural lemmas for Walk, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Walk.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SplitSat_Sizes
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace SplitSat
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight.Width
end SplitSat


