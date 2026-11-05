-- Prove2me | Definitions.Def_CircuitLowerBound_Circ_Norm
-- name    : CircuitLowerBound_Circ_Norm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:56:20.206206+00:00
-- url     : https://prove2.me/theorems/01109a42-0104-4bda-964e-df1285b67149
-- title:
--   Norm
-- statement:
--   Definitions and structural lemmas for Norm, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Norm.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace CircuitLowerBound
open ENP Groundwork
namespace Norm
def op' (n : ℕ) (G : Gate) (x y : Bool) : Bool := G.op (decide (G.in₁ < n) && x) (decide (G.in₂ < n) && y)
def ng (n : ℕ) (G : Gate) : GateD :=
  ((op' n G false false, op' n G false true, op' n G true false, op' n G true true), if G.in₁ < n then G.in₁ else 0, if G.in₂ < n then G.in₂ else 0)
def norm : ℕ → Circuit → List GateD
  | _, [] => []
  | n, G :: C => ng n G :: norm (n + 1) C
end Norm
open CircuitLowerBound.Norm
end CircuitLowerBound


