-- Prove2me | Definitions.Def_PaddedDescent_RateLemmas
-- name    : PaddedDescent_RateLemmas
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:20:29.596595+00:00
-- url     : https://prove2.me/theorems/36bf4d68-b366-40e1-a985-b0502717f46d
-- title:
--   Rate Lemmas
-- statement:
--   Definitions and structural lemmas for Rate Lemmas, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/RateLemmas.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
set_option autoImplicit false
section
section
@[expose] section
namespace Sat3
open Turing
open scoped NNReal ENNReal
end Sat3


