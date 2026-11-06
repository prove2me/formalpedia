-- Prove2me | Definitions.Def_SplitSat_Procedure
-- name    : SplitSat_Procedure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:35:59.88307+00:00
-- url     : https://prove2.me/theorems/b7b6a4f4-d86f-401c-8bbd-44d815abdde4
-- title:
--   Procedure
-- statement:
--   Definitions and structural lemmas for Procedure, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Procedure.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ThreeSatPrinted_ThmEveryDelta
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_Eight_ViaGrouping_Alg
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight Eight.ViaGrouping GraphProblems
end SplitSat


