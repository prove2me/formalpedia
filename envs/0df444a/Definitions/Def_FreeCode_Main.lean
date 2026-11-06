-- Prove2me | Definitions.Def_FreeCode_Main
-- name    : FreeCode_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:08:38.3234+00:00
-- url     : https://prove2.me/theorems/913d432d-d976-4ecc-86f9-6a6a0c50c3e3
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Reader
import Definitions.Def_FreeCode_Order
import Definitions.Def_FreeCode_Random
import Definitions.Def_FreeCode_Behind
import Definitions.Def_FreeCode_Brute
import Definitions.Def_FreeCode_Tied
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace SatFree
open Groundwork FreeCode
open scoped NNReal ENNReal
end SatFree
namespace FreeCode
open SatFree
open scoped NNReal ENNReal
end FreeCode
namespace SatFree
open Groundwork FreeCode
open scoped NNReal ENNReal
end SatFree


