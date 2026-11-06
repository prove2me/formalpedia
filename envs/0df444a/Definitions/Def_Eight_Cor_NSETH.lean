-- Prove2me | Definitions.Def_Eight_Cor_NSETH
-- name    : Eight_Cor_NSETH
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:21:22.456049+00:00
-- url     : https://prove2.me/theorems/1a1c6f9e-becb-47bf-bbaa-f8de08993816
-- title:
--   NSETH
-- statement:
--   Definitions and structural lemmas for NSETH, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/NSETH.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_NSETHDefs
import Definitions.Def_Eight_Cor_Defs
import Definitions.Def_Eight_Level_End
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_KSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_WidthK_Top_EndLemmas
import Definitions.Def_WidthK_Decode
import Definitions.Def_SparsifyWidthK_DefsProg
import Definitions.Def_GraphProblems_Host
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Eight
open Groundwork Groundwork.Prog Paper Turing
end Eight


