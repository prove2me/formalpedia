-- Prove2me | Definitions.Def_PrintedOrder_Deciding
-- name    : PrintedOrder_Deciding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:03:36.239583+00:00
-- url     : https://prove2.me/theorems/98cf84a7-32ae-4d2e-8a5d-3c213a695dc7
-- title:
--   Deciding
-- statement:
--   Definitions and structural lemmas for Deciding, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Deciding.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_SplitSat_Main
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace PrintedOrder
open Groundwork Groundwork.Prog Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
end PrintedOrder


