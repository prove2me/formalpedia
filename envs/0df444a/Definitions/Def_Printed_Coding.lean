-- Prove2me | Definitions.Def_Printed_Coding
-- name    : Printed_Coding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:42:41.580441+00:00
-- url     : https://prove2.me/theorems/822f73f0-6cb0-469b-bfe4-14a62a689a4d
-- title:
--   Coding
-- statement:
--   Definitions and structural lemmas for Coding, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_CodingDefs
import Definitions.Def_QueryMachines_Comb
import Definitions.Def_Eight_SecNetworks_Clique
import Definitions.Def_Value_Clique
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
variable {K lam : ℕ}
end Printed


