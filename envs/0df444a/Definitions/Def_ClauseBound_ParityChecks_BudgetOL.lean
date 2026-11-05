-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_BudgetOL
-- name    : ClauseBound_ParityChecks_BudgetOL
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:05:19.131181+00:00
-- url     : https://prove2.me/theorems/46fa53ba-72f5-4771-a867-f4af89a30d68
-- title:
--   Budget OL
-- statement:
--   Definitions and structural lemmas for Budget OL, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BudgetOL.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
section
namespace ClauseBound.ParityChecks.BudgetOL
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (bsum)
end ClauseBound.ParityChecks.BudgetOL


