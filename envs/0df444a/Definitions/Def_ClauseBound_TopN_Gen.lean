-- Prove2me | Definitions.Def_ClauseBound_TopN_Gen
-- name    : ClauseBound_TopN_Gen
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:00:51.003386+00:00
-- url     : https://prove2.me/theorems/5706e3b1-22b3-493d-a1a8-0f884b6473f6
-- title:
--   Gen
-- statement:
--   Definitions and structural lemmas for Gen, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Gen.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
namespace ClauseBound.TopN
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen
end ClauseBound.TopN
end
namespace ClauseBound.TopN.GenN
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN.Arith
end ClauseBound.TopN.GenN
namespace ClauseBound.TopN
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN.Arith ClauseBound.TopN.GenN
end ClauseBound.TopN


