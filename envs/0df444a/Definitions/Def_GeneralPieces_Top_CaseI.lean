-- Prove2me | Definitions.Def_GeneralPieces_Top_CaseI
-- name    : GeneralPieces_Top_CaseI
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:02:34.653837+00:00
-- url     : https://prove2.me/theorems/179f4a77-4dd4-45e2-bd95-7c0e35b2879d
-- title:
--   Case I
-- statement:
--   Definitions and structural lemmas for Case I, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/CaseI.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopNet
import Definitions.Def_CountKSat_Value
import Definitions.Def_CountKSat_InOut
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Math_SatNet
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Top
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg CountKSat
end GeneralPieces.Top


