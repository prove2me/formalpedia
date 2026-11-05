-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_MasterOL
-- name    : ClauseBound_ParityChecks_MasterOL
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:06:30.323821+00:00
-- url     : https://prove2.me/theorems/e1193372-fd83-44d7-9f0e-b3146fc47159
-- title:
--   Master OL
-- statement:
--   Definitions and structural lemmas for Master OL, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/MasterOL.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_ClauseBound_TopN_Gen
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
namespace ClauseBound.ParityChecks
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen
end ClauseBound.ParityChecks
end
namespace ClauseBound.ParityChecks.MasterOL
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.TopN.GenN
end ClauseBound.ParityChecks.MasterOL
namespace ClauseBound.ParityChecks
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.TopN.GenN
end ClauseBound.ParityChecks


