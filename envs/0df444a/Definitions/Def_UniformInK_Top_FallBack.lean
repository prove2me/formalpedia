-- Prove2me | Definitions.Def_UniformInK_Top_FallBack
-- name    : UniformInK_Top_FallBack
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:29:52.967876+00:00
-- url     : https://prove2.me/theorems/348c4092-8de7-4011-9714-9f17ab9d03cd
-- title:
--   Fall Back
-- statement:
--   Definitions and structural lemmas for Fall Back, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/FallBack.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_TopN_Gen
set_option autoImplicit false
section
section
@[expose] section
namespace UniformInK.FallBack
open ClauseBound.TopN.GenN
end UniformInK.FallBack
namespace UniformInK
open ClauseBound.TopN.GenN UniformInK.FallBack
end UniformInK


