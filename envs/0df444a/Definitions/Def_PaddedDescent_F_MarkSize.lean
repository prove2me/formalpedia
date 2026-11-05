-- Prove2me | Definitions.Def_PaddedDescent_F_MarkSize
-- name    : PaddedDescent_F_MarkSize
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:25:58.746977+00:00
-- url     : https://prove2.me/theorems/0b18fca2-24fd-476a-88ac-be358514ff5a
-- title:
--   Mark Size
-- statement:
--   Definitions and structural lemmas for Mark Size, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit false
section
namespace PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}
end PaddedDescent.F.Mark.Size
namespace PaddedDescent.F
open Mark Mark.Size Finset
end PaddedDescent.F


