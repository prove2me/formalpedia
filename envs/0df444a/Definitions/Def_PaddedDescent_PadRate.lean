-- Prove2me | Definitions.Def_PaddedDescent_PadRate
-- name    : PaddedDescent_PadRate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:46:14.126198+00:00
-- url     : https://prove2.me/theorems/d4b0a36b-1dbe-4b36-b607-18152d32dbe1
-- title:
--   Pad Rate
-- statement:
--   Definitions and structural lemmas for Pad Rate, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/PadRate.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_PaddedDescent_RateLemmas
set_option autoImplicit false
section
namespace PaddedDescent
open Groundwork Sat3 Turing
variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}
end PaddedDescent


