-- Prove2me | Definitions.Def_Suffices_Loop
-- name    : Suffices_Loop
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:24:12.045015+00:00
-- url     : https://prove2.me/theorems/b49fa3f3-e846-4cd0-9a89-b5042764f0a9
-- title:
--   Loop
-- statement:
--   Definitions and structural lemmas for Loop, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Loop.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Sizes
import Definitions.Def_Exits_Runs
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
set_option autoImplicit false
section
section
@[expose] section
namespace Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
open Groundwork.Sparsify (leaves)
end Suffices


