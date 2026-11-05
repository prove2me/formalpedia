-- Prove2me | Definitions.Def_VariableBound_Top_Budget
-- name    : VariableBound_Top_Budget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:22:32.120198+00:00
-- url     : https://prove2.me/theorems/1d3e812e-12d5-4e52-b348-d661f9d06480
-- title:
--   Budget
-- statement:
--   Definitions and structural lemmas for Budget, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/Budget.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
namespace VariableBound.Budget
open PaddedDescent.F ClauseBound.ParityChecks.BudgetOL
end VariableBound.Budget
namespace VariableBound
open PaddedDescent ClauseBound.ParityChecks.BudgetOL UniformInK VariableBound.Net
end VariableBound


