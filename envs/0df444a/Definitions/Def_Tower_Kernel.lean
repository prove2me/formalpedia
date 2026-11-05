-- Prove2me | Definitions.Def_Tower_Kernel
-- name    : Tower_Kernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:47:48.365536+00:00
-- url     : https://prove2.me/theorems/fe27d2d7-fc07-4a21-9bab-14982db80d8c
-- title:
--   Kernel
-- statement:
--   Definitions and structural lemmas for Kernel, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Kernel.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Runs
set_option autoImplicit false
section
section
@[expose] section
namespace QueryMachines.Tower
open Groundwork
variable {Q A α β : Type} {M : QueryMachine Q A α β} {O : Q → Option A} {w : Q → ℕ} {s : M.σ} {b : β} {S S' T T' : ℕ}
end QueryMachines.Tower


