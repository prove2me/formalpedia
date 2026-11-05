-- Prove2me | Definitions.Def_PaddedDescent_Reduce
-- name    : PaddedDescent_Reduce
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:51:13.103845+00:00
-- url     : https://prove2.me/theorems/bf571631-75c2-467b-b529-4c5ac29fcdb9
-- title:
--   Reduce
-- statement:
--   Definitions and structural lemmas for Reduce, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Reduce.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_PadRate
import Definitions.Def_PaddedDescent_BrutePad
import Definitions.Def_ToTuring_Poly_Decode
set_option autoImplicit false
section
namespace PaddedDescent
open Groundwork Groundwork.Decode Sat3 Turing
@[expose] public def padLog (C₀ n : ℕ) : ℕ := C₀ * (n / 2 ^ sOf n + 1)
@[expose] public def eOf (C₀ : ℕ) (x : List Bool) : ℕ := padLog C₀ (nOf x)
@[expose] public def withBrute (s₀ : ℕ) (A : List Bool × List Unit → Bool) (p : List Bool × List Unit) : Bool :=
  bif decide (sOf (nOf p.1) < s₀) then bruteA p else A p
end PaddedDescent


