-- Prove2me | Definitions.Def_StepSparsify_WalkCount
-- name    : StepSparsify_WalkCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:25:05.766337+00:00
-- url     : https://prove2.me/theorems/ec263533-180d-4730-a5a2-b3f2c09bb4db
-- title:
--   Walk Count
-- statement:
--   Definitions and structural lemmas for Walk Count, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/WalkCount.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_Walk
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_UniformInK_Tree_Stack
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSatRate_Top
import Definitions.Def_CountKSatRate_Top
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace StepSparsify
open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Top ClauseBound.TopN UniformInK SparsificationLemma
open Groundwork.Sparsify (PFml leaves round)
end StepSparsify


