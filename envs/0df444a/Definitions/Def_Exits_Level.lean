-- Prove2me | Definitions.Def_Exits_Level
-- name    : Exits_Level
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:25:54.521241+00:00
-- url     : https://prove2.me/theorems/a000248a-e154-488d-bfef-6305b24460a4
-- title:
--   Level
-- statement:
--   Definitions and structural lemmas for Level, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Level.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_SecLevel_EStar
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic.Ring
set_option autoImplicit false
section
section
@[expose] section
namespace Exits
open Groundwork Groundwork.Prog Paper Eight Eight.SecNetworks Eight.ViaGrouping
end Exits


