-- Prove2me | Definitions.Def_FromPrinted_Count
-- name    : FromPrinted_Count
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:06:39.88672+00:00
-- url     : https://prove2.me/theorems/d9496bba-d665-402c-9b5a-8e7f3db8c9c7
-- title:
--   Count
-- statement:
--   Definitions and structural lemmas for Count, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_CountDefs
import Definitions.Def_Printed_End
import Definitions.Def_SplitCount_StepOne
import Definitions.Def_SplitCount_Main
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Suffices
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
open SplitCount
namespace FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal
end FromPrinted.SplitCount


