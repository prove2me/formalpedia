-- Prove2me | Definitions.Def_UniformInK_Tree_Stack
-- name    : UniformInK_Tree_Stack
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:49:50.348205+00:00
-- url     : https://prove2.me/theorems/611f50bc-6343-4d17-a38a-e704a8b7fc6c
-- title:
--   Stack
-- statement:
--   Definitions and structural lemmas for Stack, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Tree/Stack.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Tree_Defs
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace UniformInK
open Groundwork CountKSat PaddedDescent PaddedDescent.F
end UniformInK


