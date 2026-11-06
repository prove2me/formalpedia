-- Prove2me | Definitions.Def_SizeCircuit_Cert
-- name    : SizeCircuit_Cert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:47:42.865056+00:00
-- url     : https://prove2.me/theorems/aae0ffa7-c931-403d-9ddb-70f6128f7293
-- title:
--   Cert
-- statement:
--   Definitions and structural lemmas for Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_Addition
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
@[expose] section
namespace SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
@[expose] def addStepE (n : ℕ) (st : AddState) : AddState :=
  if 3 ≤ st.1.length then
    ((n + st.2.2.2.length + 1) :: st.1.drop 3, (n + st.2.2.2.length + 4) :: st.2.1, st.2.2.1,
      st.2.2.2 ++ fullAdder (n + st.2.2.2.length) (st.1.getD 0 0) (st.1.getD 1 0) (st.1.getD 2 0))
  else if 2 ≤ st.1.length then
    ((n + st.2.2.2.length + 1) :: st.2.1, [], st.2.2.1 ++ [n + st.2.2.2.length], st.2.2.2 ++ halfAdder (st.1.getD 0 0) (st.1.getD 1 0))
  else if 1 ≤ st.1.length then (st.2.1, [], st.2.2.1 ++ [st.1.getD 0 0], st.2.2.2)
  else st
@[expose] def stateLen (m : ℕ) : ℕ := 3 * (m * (3 * (6 * m) + 2 + 2) + 2) + (5 * m * (6 * (6 * m) + 18 + 2) + 2) + 6
end SizeCircuit


