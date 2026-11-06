-- Prove2me | Definitions.Def_FreeCode_Behind
-- name    : FreeCode_Behind
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:38:54.876287+00:00
-- url     : https://prove2.me/theorems/d893ba8c-3ac9-4fdf-ba5a-562632b1a555
-- title:
--   Behind
-- statement:
--   Definitions and structural lemmas for Behind, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Behind.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace FreeCode
open Groundwork Groundwork.Prog Paper SplitSat
end FreeCode


