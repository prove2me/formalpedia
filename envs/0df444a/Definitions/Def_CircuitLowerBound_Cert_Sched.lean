-- Prove2me | Definitions.Def_CircuitLowerBound_Cert_Sched
-- name    : CircuitLowerBound_Cert_Sched
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:28:37.700046+00:00
-- url     : https://prove2.me/theorems/6ec56c6c-bcc9-4b8e-b8fc-16c8dfe12d92
-- title:
--   Sched
-- statement:
--   Definitions and structural lemmas for Sched, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/Sched.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace CircuitLowerBound.Sched
open ENP Groundwork
variable {α : Type} [Enc α]
@[expose] def leTop (a s : ℕ) : Bool := decide (s ≠ 0) && (decide (Nat.log2 s ≠ 0) && decide (2 ^ a ≤ Nat.log2 (Nat.log2 s)))
end CircuitLowerBound.Sched
namespace CircuitLowerBound
open ENP Groundwork Sched
end CircuitLowerBound


