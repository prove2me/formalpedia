-- Prove2me | Definitions.Def_Groundwork_Net_Calculus
-- name    : Groundwork_Net_Calculus
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:17.883008+00:00
-- url     : https://prove2.me/theorems/ea8134a4-3189-41f5-acb8-3dedcb0e5b50
-- title:
--   Calculus
-- statement:
--   Definitions and structural lemmas for Calculus, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Calculus.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Function
set_option autoImplicit false
section
namespace Groundwork
open Finset
variable {ι X' τ A α : Type*}
namespace Cross
@[expose] public def X [DecidableEq α] (x y u v : α) : ℤ := if x = v ∧ y = u then 1 else 0
end Cross
end Groundwork


