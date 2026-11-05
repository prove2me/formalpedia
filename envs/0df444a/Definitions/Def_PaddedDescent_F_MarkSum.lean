-- Prove2me | Definitions.Def_PaddedDescent_F_MarkSum
-- name    : PaddedDescent_F_MarkSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:17:29.825066+00:00
-- url     : https://prove2.me/theorems/94d5ec6e-2313-4d2e-ba03-4e8f6e53c9d0
-- title:
--   Mark Sum
-- statement:
--   Definitions and structural lemmas for Mark Sum, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSum.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
section
namespace PaddedDescent.F.Mark.Sum
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
end PaddedDescent.F.Mark.Sum


