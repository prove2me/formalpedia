-- Prove2me | Definitions.Def_ToTuring_Closure_Basic
-- name    : ToTuring_Closure_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:45:25.187754+00:00
-- url     : https://prove2.me/theorems/09bd6d8c-12e1-46df-8906-6dbc81a9dc8a
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
set_option autoImplicit false
section
section
namespace Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
section ops
variable (M A B N : List Sym)
end ops
end Groundwork.PolyT


