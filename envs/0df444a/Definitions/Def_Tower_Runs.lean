-- Prove2me | Definitions.Def_Tower_Runs
-- name    : Tower_Runs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:19:40.921499+00:00
-- url     : https://prove2.me/theorems/a528d493-859f-4f8a-a0d2-abf3b6b72c77
-- title:
--   Runs
-- statement:
--   Definitions and structural lemmas for Runs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Definitions.Def_Tower_Kernel
set_option autoImplicit false
section
section
@[expose] section
namespace QueryMachines.Tower
open Groundwork
variable {Q A α β : Type} (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β)
end QueryMachines.Tower


