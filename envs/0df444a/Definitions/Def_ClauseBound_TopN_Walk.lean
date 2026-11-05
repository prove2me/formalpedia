-- Prove2me | Definitions.Def_ClauseBound_TopN_Walk
-- name    : ClauseBound_TopN_Walk
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:15:45.505635+00:00
-- url     : https://prove2.me/theorems/9a3e30f0-8bfa-4fc9-9e82-30f5effd64c6
-- title:
--   Walk
-- statement:
--   Definitions and structural lemmas for Walk, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Walk.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_CountKSatRate_Top
import Definitions.Def_CountKSatRate_Top
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
namespace ClauseBound.TopN
open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Top
open Groundwork.Sparsify (PFml leaves round)
open WidthK (theta bsum leafC)
end ClauseBound.TopN


