-- Prove2me | Definitions.Def_ThreeSatOnTree_ThmEveryDelta
-- name    : ThreeSatOnTree_ThmEveryDelta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:14:33.064651+00:00
-- url     : https://prove2.me/theorems/cebac5cd-096b-452d-8b4a-9111793c81db
-- title:
--   Thm Every Delta
-- statement:
--   Definitions and structural lemmas for Thm Every Delta, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatOnTree/ThmEveryDelta.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatOnTree_Defs
import Definitions.Def_Eight_SecProof_Proof
import Definitions.Def_SparsificationLemma_TreeWalk_Walk
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_WidthK_Poly_Decode
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
section
section
@[expose] section
namespace ThreeSatOnTree
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight SparsificationLemma.TreeWalk
end ThreeSatOnTree


