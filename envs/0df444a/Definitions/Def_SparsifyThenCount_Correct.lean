-- Prove2me | Definitions.Def_SparsifyThenCount_Correct
-- name    : SparsifyThenCount_Correct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:33:35.698481+00:00
-- url     : https://prove2.me/theorems/4b22acf9-c9ce-46bb-b4f5-43d7fba15117
-- title:
--   Correct
-- statement:
--   Definitions and structural lemmas for Correct, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/Correct.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_VariableBound_Top_Correct
import Definitions.Def_VariableBound_Top_Correct
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
namespace SparsifyThenCount
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.Correct VariableBound VariableBound.Correct VariableBound.Net
open PaddedDescent.F.Mark (WfL occ nSat)
end SparsifyThenCount


