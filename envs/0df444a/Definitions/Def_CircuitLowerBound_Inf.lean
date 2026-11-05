-- Prove2me | Definitions.Def_CircuitLowerBound_Inf
-- name    : CircuitLowerBound_Inf
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:20:45.864928+00:00
-- url     : https://prove2.me/theorems/63473c9c-f371-4fe7-98a9-a0838a95921e
-- title:
--   Inf
-- statement:
--   Definitions and structural lemmas for Inf, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
@[expose] section
namespace CircuitLowerBound.Inf
open ENP
def Avail (n : ℕ) (C : Circuit) (g : List Bool → Bool) : Prop := ∃ w, w < n + C.length ∧ ∀ x : List Bool, x.length = n → (wires x C).getD w false = g x
def Ext (n : ℕ) (g : List Bool → Bool) : Prop := ∀ C₀ : Circuit, ∃ D : Circuit, Avail n (C₀ ++ D) g
end CircuitLowerBound.Inf


