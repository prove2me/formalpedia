-- Prove2me | Definitions.Def_Variance_Grouping
-- name    : Variance_Grouping
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:22:02.68582+00:00
-- url     : https://prove2.me/theorems/2f9b387d-6591-4a5d-a5c8-672193ef9de9
-- title:
--   Grouping
-- statement:
--   Definitions and structural lemmas for Grouping, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Var
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_Eight_SecNetworks_Grouping
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace Variance
open Finset Eight.SecNetworks Eight.ViaGrouping
end Variance


