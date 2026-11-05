-- Prove2me | Definitions.Def_Eight_SecNetworks_Grouping
-- name    : Eight_SecNetworks_Grouping
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:58:26.973781+00:00
-- url     : https://prove2.me/theorems/e7f82f6f-0c23-411e-8273-5a787494f76f
-- title:
--   Sec Networks Grouping
-- statement:
--   Definitions and structural lemmas for Sec Networks Grouping, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_Colouring
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace Eight.SecNetworks
open Finset Groundwork.Colouring
variable {g K : ℕ}
def off (c : Fin g → Fin g → ℕ) (a b : Fin g) : ℕ := if b ≠ a then c a b else 0
end Eight.SecNetworks


