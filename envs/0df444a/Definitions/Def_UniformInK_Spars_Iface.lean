-- Prove2me | Definitions.Def_UniformInK_Spars_Iface
-- name    : UniformInK_Spars_Iface
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:41:29.659254+00:00
-- url     : https://prove2.me/theorems/cc1301cb-d16a-45ed-8423-d2a4ddf16ad6
-- title:
--   Iface
-- statement:
--   Definitions and structural lemmas for Iface, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Iface.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
set_option autoImplicit false
section
section
@[expose] section
namespace UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK WidthK.Prog WidthK.ProgMain
end UniformInK


