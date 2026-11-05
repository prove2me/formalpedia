-- Prove2me | Definitions.Def_GeneralPieces_Half_List
-- name    : GeneralPieces_Half_List
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:22:03.825473+00:00
-- url     : https://prove2.me/theorems/10a458b6-c498-45ab-bde0-acd906af3859
-- title:
--   List
-- statement:
--   Definitions and structural lemmas for List, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
@[expose] def toPNats (L : List ℕ) : List ℕ+ := L.map Nat.toPNat'
@[expose] def ptn (L : List ℕ) : Ptn := (toPNats L : Multiset ℕ+)
namespace Half
@[expose] noncomputable def polyK (k : ℤ × List ℕ → ℚ) (A : ClauseBound.Boson.FA) : V := (A.map fun c => k c • tpow (ptn c.2)).sum
@[expose] noncomputable def polyOf (A : ClauseBound.Boson.FA) : V := polyK (fun c => (c.1 : ℚ)) A
end Half
open Half
section
variable {lam h : ℕ} {ℓ : Pieces.Bits lam → List ℕ}
end
end GeneralPieces


