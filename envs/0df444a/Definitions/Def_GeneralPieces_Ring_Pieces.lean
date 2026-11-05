-- Prove2me | Definitions.Def_GeneralPieces_Ring_Pieces
-- name    : GeneralPieces_Ring_Pieces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:29:02.983091+00:00
-- url     : https://prove2.me/theorems/da3fad2d-1169-464e-bca9-2e0c921df110
-- title:
--   Pieces
-- statement:
--   Definitions and structural lemmas for Pieces, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
@[expose] def Le (h : ℕ) (a : V) : Prop := ∀ π, coef π a ≠ 0 → wt π ≤ h
end GeneralPieces.Pcs
namespace GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ GeneralPieces.Pcs
end GeneralPieces


