-- Prove2me | Definitions.Def_ClauseBound_Alg_TopVal
-- name    : ClauseBound_Alg_TopVal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:55:35.248023+00:00
-- url     : https://prove2.me/theorems/8c5370bd-b7eb-416c-bfdd-3d8692a82a32
-- title:
--   Top Val
-- statement:
--   Definitions and structural lemmas for Top Val, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopVal.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_CountKSat_Value
import Definitions.Def_CountKSat_InOut
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
namespace ClauseBound.Alg.TopVal
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F CountKSat
end ClauseBound.Alg.TopVal


