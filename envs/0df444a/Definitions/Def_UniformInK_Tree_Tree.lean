-- Prove2me | Definitions.Def_UniformInK_Tree_Tree
-- name    : UniformInK_Tree_Tree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:52:20.959395+00:00
-- url     : https://prove2.me/theorems/503eb0c5-e2ef-4042-ac5a-ad5b50714437
-- title:
--   Tree
-- statement:
--   Definitions and structural lemmas for Tree, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Tree/Tree.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Tree_Defs
import Definitions.Def_CountKSatRate_Tree
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace UniformInK
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate WidthK.Prog
namespace Tree
end Tree
end UniformInK


