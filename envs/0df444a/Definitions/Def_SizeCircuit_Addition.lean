-- Prove2me | Definitions.Def_SizeCircuit_Addition
-- name    : SizeCircuit_Addition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:41:11.335648+00:00
-- url     : https://prove2.me/theorems/72ee14e8-f1e7-4be6-961e-30178a857108
-- title:
--   Addition
-- statement:
--   Definitions and structural lemmas for Addition, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
@[expose] section
namespace SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
@[expose] def AddGood (n : ℕ) (st : AddState) : Prop :=
  (∀ x ∈ st.1, x < n + st.2.2.2.length) ∧ (∀ x ∈ st.2.1, x < n + st.2.2.2.length) ∧ (∀ x ∈ st.2.2.1, x < n + st.2.2.2.length) ∧
    WFa n st.2.2.2 ∧ (st.1 = [] → st.2.1 = [])
@[expose] def onesAmong (v : ℕ → Bool) (l : List ℕ) : ℕ := (l.map fun x => (v x).toNat).sum
@[expose] def addValue (v : ℕ → Bool) (st : AddState) : ℕ := ofWord (st.2.2.1.map v) + 2 ^ st.2.2.1.length * (onesAmong v st.1 + 2 * onesAmong v st.2.1)
end SizeCircuit


