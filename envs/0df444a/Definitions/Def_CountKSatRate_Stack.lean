-- Prove2me | Definitions.Def_CountKSatRate_Stack
-- name    : CountKSatRate_Stack
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:43:19.219629+00:00
-- url     : https://prove2.me/theorems/a8ab80db-bf6a-4e6e-b5a1-a5bc33ab275d
-- title:
--   Stack
-- statement:
--   Definitions and structural lemmas for Stack, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Stack.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
namespace CountKSatRate
open Groundwork CountKSat PaddedDescent PaddedDescent.F
open WidthK (bsum)
end CountKSatRate


