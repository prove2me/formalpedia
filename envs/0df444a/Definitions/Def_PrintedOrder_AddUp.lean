-- Prove2me | Definitions.Def_PrintedOrder_AddUp
-- name    : PrintedOrder_AddUp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:42:45.06438+00:00
-- url     : https://prove2.me/theorems/e0673c80-cc30-49c9-9dbe-a2681aad7d3d
-- title:
--   Add Up
-- statement:
--   Definitions and structural lemmas for Add Up, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_SplitCount_Disjoint
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SparsificationLemma_One
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace PrintedOrder
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat SplitCount
end PrintedOrder


