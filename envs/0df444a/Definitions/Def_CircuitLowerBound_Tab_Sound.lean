-- Prove2me | Definitions.Def_CircuitLowerBound_Tab_Sound
-- name    : CircuitLowerBound_Tab_Sound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:57:16.024724+00:00
-- url     : https://prove2.me/theorems/4da11fae-c21a-4656-9c8d-562d343e4357
-- title:
--   Sound
-- statement:
--   Definitions and structural lemmas for Sound, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
structure Enc (α : Atom N → ℕ → ℕ → Bool) (t V : ℕ) (c : N.tm.Cfg) : Prop where
  lab : ∀ x, α (.lab x) t 0 = true ↔ x = c.l
  var : ∀ x, α (.var x) t 0 = true ↔ x = c.var
  cell : ∀ k x q, q < V → (α (.cell k x) t q = true ↔ x = (c.stk k)[q]?)
variable {N} [Finite (Case N)] {α : Atom N → ℕ → ℕ → Bool} {b Q P : ℕ}
end CircuitLowerBound.Tab


