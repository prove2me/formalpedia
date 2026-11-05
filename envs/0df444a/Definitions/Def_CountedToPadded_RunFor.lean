-- Prove2me | Definitions.Def_CountedToPadded_RunFor
-- name    : CountedToPadded_RunFor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:56:58.595368+00:00
-- url     : https://prove2.me/theorems/140a0cea-fdd2-491c-99da-8af4c472a9b2
-- title:
--   Run For
-- statement:
--   Definitions and structural lemmas for Run For, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Compare
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
set_option autoImplicit false
section
section
@[expose] section
namespace QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F
section right
variable {α β : Type} {N : Stepped α β} [Enc N.σ] [Carried N.σ] {S room : ℕ} {b : β}
end right
end QueryMachines.Bridge.Proof
namespace QueryMachines.Bridge
open Groundwork Groundwork.PolyT PaddedDescent.F Proof
end QueryMachines.Bridge


