-- Prove2me | Definitions.Def_Printed_Achievable
-- name    : Printed_Achievable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:49:37.766413+00:00
-- url     : https://prove2.me/theorems/a46774ed-123a-483d-9520-4b017206e32e
-- title:
--   Achievable
-- statement:
--   Definitions and structural lemmas for Achievable, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Achievable.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Absorb
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
end Printed


