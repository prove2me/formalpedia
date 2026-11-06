-- Prove2me | Definitions.Def_SplitSat_Simulate
-- name    : SplitSat_Simulate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:27:45.112047+00:00
-- url     : https://prove2.me/theorems/6a36c0ad-00e0-492c-9c58-7741059946b8
-- title:
--   Simulate
-- statement:
--   Definitions and structural lemmas for Simulate, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Simulate.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace SplitSat
open Groundwork Groundwork.Prog Paper CountKSat Eight.ViaGrouping
end SplitSat


