-- Prove2me | Definitions.Def_VariableBound_Net_SizeSmall
-- name    : VariableBound_Net_SizeSmall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:09:53.358604+00:00
-- url     : https://prove2.me/theorems/a0809d17-e33f-4343-9d51-8e5d11b53522
-- title:
--   Size Small
-- statement:
--   Definitions and structural lemmas for Size Small, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeSmall.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_SizeP
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Net.SizeSmall
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (qv occ)
variable {k g n Δ : ℕ}
end VariableBound.Net.SizeSmall


