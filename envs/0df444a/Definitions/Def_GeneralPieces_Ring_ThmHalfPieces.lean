-- Prove2me | Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
-- name    : GeneralPieces_Ring_ThmHalfPieces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:23:14.496789+00:00
-- url     : https://prove2.me/theorems/5c514835-f176-4a6b-b68d-d78c3652b2f6
-- title:
--   Thm Half Pieces
-- statement:
--   Definitions and structural lemmas for Thm Half Pieces, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/ThmHalfPieces.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
@[expose] noncomputable def fa (h i : ℕ) (r : ℤ) (ξ σ' σ : Ptn) : ℤ := (-1) ^ i * (coef σ' (op (angle h i (aFam ξ)) r (tpow σ))).num
@[expose] noncomputable def fb (r : ℤ) (ν σ' σ : Ptn) : ℤ := (coef σ' (op (bFam ν) r (tpow σ))).num
@[expose] noncomputable def fam {lam : ℕ} (h : ℕ) (mu : Pieces.Bits lam → Ptn) : Pieces.Family lam where
  d := h.factorial
  I := Icc (-(2 * h : ℤ)) (2 * h)
  A := fun s x y u v => (piece h mu s x y u v).num
  crow := fun s => Nat.clog 2 (Rrow h s)
  ccol := fun s => Nat.clog 2 (Rcol h s)
section
variable {lam h : ℕ} {mu : Pieces.Bits lam → Ptn}
end
end GeneralPieces.ThmHalfPieces
namespace GeneralPieces
open AppHalfPieces Finset GeneralPieces.ThmHalfPieces ClauseBound.Boson.Final
end GeneralPieces


