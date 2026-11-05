-- Prove2me | Definitions.Def_Exits_Tested
-- name    : Exits_Tested
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:47:02.505282+00:00
-- url     : https://prove2.me/theorems/7a2b2ab6-087f-47dc-aff4-4f94b69cbb57
-- title:
--   Tested
-- statement:
--   Definitions and structural lemmas for Tested, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Defs
set_option autoImplicit false
section
section
@[expose] section
namespace Exits
open Groundwork Groundwork.Stepped
variable {α β γ τ ν : Type}
section sel
variable (sel : τ → Option ν) (v : ν → Bool) (w : τ → Bool) (hw : ∀ x, w x = ((sel x).map v).getD false)
include hw
end sel
end Exits


