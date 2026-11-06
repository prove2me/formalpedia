-- Prove2me | Definitions.Def_VariableBound_MainPrinted
-- name    : VariableBound_MainPrinted
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:07:25.594551+00:00
-- url     : https://prove2.me/theorems/60fcacfd-8573-4aea-a1b5-b919a0ecda3d
-- title:
--   Main Printed
-- statement:
--   Definitions and structural lemmas for Main Printed, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/MainPrinted.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInKStatement
import Definitions.Def_VariableBound_Printed_TiedDefs
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_VariableBound_Printed_Tied
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_VariableBound_Paper_Decide
import Definitions.Def_VariableBound_Top_Time
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_VariableBound_StepParity
import Definitions.Def_VariableBound_Family_Main
import Definitions.Def_VariableBound_Field_Family
import Definitions.Def_VariableBound_Field_Cert
import Definitions.Def_VariableBound_Params_Spec
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_VariableBound_Params_Cert
import Definitions.Def_VariableBound_Search_Correct
import Definitions.Def_VariableBound_Search_Cert
import Definitions.Def_VariableBound_Net_Main
import Definitions.Def_VariableBound_Count_Correct
import Definitions.Def_VariableBound_Count_Cert
import Definitions.Def_VariableBound_Top_Budget
import Definitions.Def_VariableBound_Top_Correct
import Definitions.Def_VariableBound_Top_CorrectB
import Definitions.Def_VariableBound_Top_Arith
import Definitions.Def_VariableBound_Cert_Top
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_CorrectB
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_UniformInK_Tree_Tree
import Definitions.Def_UniformInK_Tree_Defs
import Definitions.Def_UniformInK_Tree_Stack
import Definitions.Def_UniformInK_Spars_Main
import Definitions.Def_UniformInK_Cert_Walk
import Definitions.Def_ClauseBound_MainBoth
import Definitions.Def_ClauseBound_Both_TimeM
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Alg_TopVal
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_CountKSatRate_Walk
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSat_InOut
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Both ClauseBound.ParityChecks UniformInK VariableBound.Decide
end VariableBound
namespace SatM
end SatM


