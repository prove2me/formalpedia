-- Prove2me | Definitions.Def_ToTuring_Bound
-- name    : ToTuring_Bound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:21:02.256461+00:00
-- url     : https://prove2.me/theorems/2a33d289-4350-40c8-87e2-6886115ebe94
-- title:
--   Bound
-- statement:
--   Definitions and structural lemmas for Bound, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Bound.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Basic
set_option autoImplicit false
section
section
namespace Groundwork
def PB (t : ℕ → ℕ) : Prop := ∃ c : ℕ, ∀ n, t n ≤ c * (n + 1) ^ c
namespace PB
variable {t s : ℕ → ℕ}
end PB
end Groundwork


