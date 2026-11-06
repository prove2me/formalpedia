-- Prove2me | Definitions.Def_SplitCount_Main
-- name    : SplitCount_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:58:26.525613+00:00
-- url     : https://prove2.me/theorems/060ba3fa-1322-4387-86fc-b36f4a460cdf
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_StepOne
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Suffices
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
section
section
@[expose] section
namespace SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal
end SplitCount


