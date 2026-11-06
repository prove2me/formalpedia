-- Prove2me | Definitions.Def_SparsifyThenCount_PlanUsed
-- name    : SparsifyThenCount_PlanUsed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:27:51.0621+00:00
-- url     : https://prove2.me/theorems/846c2273-4adc-4619-ae7b-0f81307bb35a
-- title:
--   Plan Used
-- statement:
--   Definitions and structural lemmas for Plan Used, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsed.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_PlanUsedDefs
import Definitions.Def_SparsifyThenCount_Main
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_ClauseBound_Alg_Decode
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
section
section
@[expose] section
namespace SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK VariableBound VariableBound.Decide Filter
namespace PlanUsedL
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (slU : U → U)
end
end PlanUsedL
open PlanUsedL
end SparsifyThenCount


