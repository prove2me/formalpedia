-- Prove2me | Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
-- name    : CircuitLowerBoundInfinitelyOftenStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:32:35.940624+00:00
-- url     : https://prove2.me/theorems/1b2ec4f0-9152-4d3b-90f6-ffeeb319df8d
-- title:
--   Circuit Lower Bound Infinitely Often Statement
-- statement:
--   Definitions and structural lemmas for Circuit Lower Bound Infinitely Often Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/CircuitLowerBoundInfinitelyOftenStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundStatement
set_option autoImplicit false
section
section
namespace ENP
def DecidedAt (L : Lang) (s n : ℕ) : Prop := ∃ C : Circuit, C.length ≤ s ∧ ∀ x : List Bool, x.length = n → (eval C x = true ↔ L x)
def CorCircuitsInf : Prop := ∃ L : Lang, InENP L ∧ ∀ c N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬DecidedAt L (c * (n + 1)) n
def AllDecided : Prop := ∀ (L : Lang) (n : ℕ), ∃ s : ℕ, DecidedAt L s n
end ENP


