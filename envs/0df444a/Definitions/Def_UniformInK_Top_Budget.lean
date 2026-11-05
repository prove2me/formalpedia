-- Prove2me | Definitions.Def_UniformInK_Top_Budget
-- name    : UniformInK_Top_Budget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:20:42.044478+00:00
-- url     : https://prove2.me/theorems/3f52197d-5ad3-4c72-a8af-8d39a555a513
-- title:
--   Budget
-- statement:
--   Definitions and structural lemmas for Budget, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Budget.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
namespace UniformInK.Budget
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL UniformInK.Leaves
end UniformInK.Budget
namespace UniformInK
open PaddedDescent ClauseBound.ParityChecks.BudgetOL UniformInK.Leaves UniformInK.Budget
end UniformInK


