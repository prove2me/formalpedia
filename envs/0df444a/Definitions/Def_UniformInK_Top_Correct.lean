-- Prove2me | Definitions.Def_UniformInK_Top_Correct
-- name    : UniformInK_Top_Correct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:21:31.54426+00:00
-- url     : https://prove2.me/theorems/6e96d092-284f-425f-8686-37060f766a2b
-- title:
--   Correct
-- statement:
--   Definitions and structural lemmas for Correct, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Correct.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
namespace UniformInK.Correct
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.ParityChecks.TopOL
open PaddedDescent.F.Mark (WfL occ nSat)
end UniformInK.Correct
namespace UniformInK
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.ParityChecks.TopOL UniformInK.Correct
open PaddedDescent.F.Mark (WfL occ nSat)
end UniformInK


