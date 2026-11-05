-- Prove2me | Definitions.Def_Eight_ViaGrouping_Search
-- name    : Eight_ViaGrouping_Search
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:49:37.632887+00:00
-- url     : https://prove2.me/theorems/838be47d-883d-4c11-8694-8f660d30ad9a
-- title:
--   Search
-- statement:
--   Definitions and structural lemmas for Search, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g K : ℕ} {N : Net g} {P B τ S : ℕ}
end Eight.ViaGrouping


