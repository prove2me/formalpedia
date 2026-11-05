-- Prove2me | Definitions.Def_SingleBitPieces_SecCrossing_PolyA
-- name    : SingleBitPieces_SecCrossing_PolyA
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:10:01.815882+00:00
-- url     : https://prove2.me/theorems/441f4b70-2e8a-4405-83ef-85b5f6285e01
-- title:
--   Sec Crossing Poly A
-- statement:
--   Definitions and structural lemmas for Sec Crossing Poly A, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/SecCrossing_PolyA.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecCrossing_Crossing
import Definitions.Def_PaddedDescent_F_FuelCert
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Log
set_option autoImplicit false
section
section
@[expose] section
namespace SingleBitPieces
open Groundwork PaddedDescent.F Finset
namespace SecCrossing_PolyA
variable {α : Type} [Enc α]
end SecCrossing_PolyA
open SecCrossing_PolyA
end SingleBitPieces


