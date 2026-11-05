-- Prove2me | Definitions.Def_CountKSatRate_Leaf
-- name    : CountKSatRate_Leaf
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:16:52.926974+00:00
-- url     : https://prove2.me/theorems/26bf741a-e558-4990-b190-6524a100b0ee
-- title:
--   Leaf
-- statement:
--   Definitions and structural lemmas for Leaf, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Leaf.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
set_option autoImplicit false
section
namespace CountKSatRate.Leaf
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open PaddedDescent.F.Mark (occ nSat WfL)
end CountKSatRate.Leaf


