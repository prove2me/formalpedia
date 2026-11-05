-- Prove2me | Definitions.Def_ThreeSatOnTree_Defs
-- name    : ThreeSatOnTree_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:08:01.735085+00:00
-- url     : https://prove2.me/theorems/89d9f6f2-0df9-4e23-bf15-5a89b242fc74
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatOnTree/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_WidthK_Top_Sat
import Definitions.Def_WidthK_Decode
import Definitions.Def_SparsifyWidthK_DefsProg
import Definitions.Def_UniformInK_Spars_Defs
set_option autoImplicit false
section
section
namespace ThreeSatOnTree
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper
def satC (τ : ℕ) (Mc : StepMachine Formula ℤ) : StepMachine (List Bool) Bool := satMK (DecodeK.decK 3) (stepK (thetaU τ) 3) rootP Mc
end ThreeSatOnTree


