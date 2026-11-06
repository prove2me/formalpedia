-- Prove2me | Definitions.Def_PrintedOrder_Counting
-- name    : PrintedOrder_Counting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:06:39.947546+00:00
-- url     : https://prove2.me/theorems/a1ca4bfa-3acb-44be-a11f-9425d25ec5aa
-- title:
--   Counting
-- statement:
--   Definitions and structural lemmas for Counting, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Counting.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_PrintedOrder_AddUp
import Definitions.Def_SplitCount_Main
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace PrintedOrder
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ SplitCount
open scoped NNReal
end PrintedOrder


