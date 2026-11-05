-- Prove2me | Definitions.Def_GeneralPieces_Ring_Defs
-- name    : GeneralPieces_Ring_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:26:33.084195+00:00
-- url     : https://prove2.me/theorems/02abd7e7-7ff9-4c88-b9ab-2d468d6b55f2
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppHalfPiecesStatement
import Definitions.Def_ClauseBound_Boson_Defs2
set_option autoImplicit false
section
section
namespace GeneralPieces
open AppHalfPieces
def toN (μ : Ptn) : Multiset ℕ := μ.map fun k : ℕ+ => (k : ℕ)
def toL (a : List ℕ+) : List ℕ := a.map fun k : ℕ+ => (k : ℕ)
def StBridge : Prop := ∀ (a : List ℕ+) (r : ℤ) (π σ : Ptn), coef π (opMon a r (tpow σ)) = (ClauseBound.Boson.op (toL a) r (toN π) (toN σ) : ℚ)
end GeneralPieces


