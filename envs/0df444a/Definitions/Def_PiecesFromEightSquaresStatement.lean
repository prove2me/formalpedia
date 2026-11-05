-- Prove2me | Definitions.Def_PiecesFromEightSquaresStatement
-- name    : PiecesFromEightSquaresStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:57:11.076193+00:00
-- url     : https://prove2.me/theorems/ff07f3f1-4a58-4861-9250-93103a4c5322
-- title:
--   Pieces From Eight Squares Statement
-- statement:
--   Definitions and structural lemmas for Pieces From Eight Squares Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/PiecesFromEightSquaresStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_DefGenPieces_Progs
import Definitions.Def_GeneralPieces_Tied_Defs
import Definitions.Def_Eight_SecCrossing_PolyDefs
set_option autoImplicit false
section
section
namespace AppRunningTime
open Eight
def valEight (q : ValQ) : ℤ := aMul (q.2.1.2, q.2.2)
def LemPiecesPieces : Prop := ∀ c : ℕ, 8 ≤ c → IsPieces (11 / 12) c eightF A valEight ∧
  ∀ lam, 1 ≤ lam → eightF.cnt 0 lam = tOf lam + 1 ∧ eightF.d 0 lam = 2 ^ tOf lam ∧
    ∀ i ≤ tOf lam, eightF.cap false 0 lam i = crow lam i ∧ eightF.cap true 0 lam i = ccol lam i ∧ ((crow lam i + ccol lam i : ℕ) : ℝ) ≤ 11 * lam / 3 + 8
end AppRunningTime


