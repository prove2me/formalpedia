-- Prove2me | Definitions.Def_RecursionWithPieces_Master
-- name    : RecursionWithPieces_Master
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:30:55.789227+00:00
-- url     : https://prove2.me/theorems/0acba053-1eed-4425-8d50-b5ba9941e889
-- title:
--   Master
-- statement:
--   Definitions and structural lemmas for Master, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Master.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionWithPieces_Defs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_UniformInK_Top_FallBack
import Definitions.Def_ClauseBound_MainBoth
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_Alg_Need
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace RecursionWithPieces
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks ClauseBound.Both UniformInK VariableBound GeneralPieces
end RecursionWithPieces


