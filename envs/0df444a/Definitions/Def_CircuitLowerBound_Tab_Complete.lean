-- Prove2me | Definitions.Def_CircuitLowerBound_Tab_Complete
-- name    : CircuitLowerBound_Tab_Complete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T18:01:47.224648+00:00
-- url     : https://prove2.me/theorems/dafdc788-2c3c-42e6-9a6e-a27e3ac30629
-- title:
--   Complete
-- statement:
--   Definitions and structural lemmas for Complete, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Complete.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool) [Finite (Case N)]
open Classical in
/-- The truth values of all statements about the rows c 0, c 1, … -/
noncomputable def rows (c : ℕ → N.tm.Cfg) (P : ℕ) : Atom N → ℕ → ℕ → Bool
  | .lab x, t, _ => decide (x = (c t).l)
  | .var x, t, _ => decide (x = (c t).var)
  | .len k n, t, _ => decide ((n : ℕ) = ((nxt N (caseOf N (c t))).stk k).length)
  | .cell k x, t, q => decide (x = ((c t).stk k)[q]?)
  | .cs γ, t, _ => decide (γ = caseOf N (c t))
  | .pre i, t, _ => decide (((ec N (caseOf N (c t)) : Fin (nc N)) : ℕ) < i)
  | .u, _, q => decide (q ≤ P)
variable {N}
end CircuitLowerBound.Tab
namespace CircuitLowerBound
open Tab
end CircuitLowerBound


