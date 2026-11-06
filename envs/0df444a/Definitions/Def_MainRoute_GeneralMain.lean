-- Prove2me | Definitions.Def_MainRoute_GeneralMain
-- name    : MainRoute_GeneralMain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:18:27.392944+00:00
-- url     : https://prove2.me/theorems/889cb280-d66b-43b1-901f-e0cea86dda65
-- title:
--   General Main
-- statement:
--   Definitions and structural lemmas for General Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/GeneralMain.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_GeneralDefs
import Definitions.Def_MainRoute_General
import Definitions.Def_MainRoute_GeneralInM
import Definitions.Def_MinOfBounds_Main
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_PairsToBound_Main
import Definitions.Def_RecursionToBound_Main
set_option autoImplicit false
section
section
@[expose] section
namespace MainRoute
open MinOfBounds PairsToBound
end MainRoute


