-- Prove2me | Definitions.Def_CircuitLowerBound_Small
-- name    : CircuitLowerBound_Small
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:53:38.106202+00:00
-- url     : https://prove2.me/theorems/8e21ddd7-bf75-46ec-83a6-db44bf58b073
-- title:
--   Small
-- statement:
--   Definitions and structural lemmas for Small, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace CircuitLowerBound
open ENP Groundwork
namespace SmallFacts
def n5 (l : TLit) : List ℕ := [l.1, l.2.1, l.2.2.1, l.2.2.2.1, l.2.2.2.2.toNat]
def n15 (c : TCl) : List ℕ := n5 c.1 ++ n5 c.2.1 ++ n5 c.2.2
end SmallFacts
open SmallFacts
end CircuitLowerBound


