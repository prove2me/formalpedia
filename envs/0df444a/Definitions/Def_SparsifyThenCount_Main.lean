-- Prove2me | Definitions.Def_SparsifyThenCount_Main
-- name    : SparsifyThenCount_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:18:58.102227+00:00
-- url     : https://prove2.me/theorems/c1b6cba0-140a-4216-9434-bda7f90ddf27
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInKStatement
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_SparsifyThenCount_Correct
import Definitions.Def_SparsifyThenCount_CorrectB
import Definitions.Def_SparsifyThenCount_CertTop
import Definitions.Def_SparsifyThenCount_CertBoth
import Definitions.Def_SparsifyThenCount_Tied
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_VariableBound_Printed_Tied
import Definitions.Def_VariableBound_Printed_TiedDefs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_VariableBound_Paper_Decide
import Definitions.Def_VariableBound_Printed_VariablesA_Main
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Top_Time
import Definitions.Def_VariableBound_Top_Budget
import Definitions.Def_VariableBound_Top_CorrectB
import Definitions.Def_VariableBound_Top_Arith
import Definitions.Def_VariableBound_Top_ArithPlan
import Definitions.Def_StepSparsify_WalkCount
import Definitions.Def_StepSparsify_CertWalk
import Definitions.Def_StepSparsify_CalServes
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_CorrectB
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_ClauseBound_MainBoth
import Definitions.Def_ClauseBound_Both_TimeM
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Alg_TopVal
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_CountKSatRate_Brute
set_option autoImplicit false
section
section
@[expose] section
namespace SparsifyThenCount
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Both ClauseBound.ParityChecks ClauseBound.TopN UniformInK VariableBound VariableBound.Decide
end SparsifyThenCount
namespace SatM
end SatM
namespace MainTheoremForms
open CountKSatRate ClauseBound.Alg
end MainTheoremForms


