-- Prove2me | Definitions.Def_GeneralPieces_Tied_BoundDefs
-- name    : GeneralPieces_Tied_BoundDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:34:22.183073+00:00
-- url     : https://prove2.me/theorems/42f243da-1586-4892-affc-a1428d2ca553
-- title:
--   Bound Defs
-- statement:
--   Definitions and structural lemmas for Bound Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Tied/BoundDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_Defs
import Definitions.Def_GeneralPieces_DefGenPieces_Progs
set_option autoImplicit false
section
section
namespace GeneralPieces.Tied
open Groundwork PaddedDescent.F ClauseBound.Alg AppRunningTime
def IsPiecesB (c : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : ValQ → ℤ) : Prop := IsPieces (1 / Real.sqrt 2) c P A val ∧
  ∀ lam, 1 ≤ lam → ∃ mu : Pieces.Bits lam → AppHalfPieces.Ptn, AppHalfPieces.IsMu lam (AppHalfPieces.hOf lam) mu ∧
    P.cnt 0 lam = 4 * AppHalfPieces.hOf lam + 1 ∧ P.d 0 lam = (AppHalfPieces.hOf lam).factorial ∧
    ∀ i < P.cnt 0 lam, (∀ x y u v, (A lam i x y u v : ℚ) = AppHalfPieces.piece (AppHalfPieces.hOf lam) mu ((i : ℤ) - 2 * AppHalfPieces.hOf lam) x y u v) ∧
      P.cap false 0 lam i = Nat.clog 2 (AppHalfPieces.Rrow (AppHalfPieces.hOf lam) ((i : ℤ) - 2 * AppHalfPieces.hOf lam)) ∧
      P.cap true 0 lam i = Nat.clog 2 (AppHalfPieces.Rcol (AppHalfPieces.hOf lam) ((i : ℤ) - 2 * AppHalfPieces.hOf lam))
def recOf (P : PiecesF) (val : ValQ → ℤ) (c : ℕ) : PiecesF := atZero (trimV P val c) c 1
def ThmRunningTimeCm : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : ValQ → ℤ), IsPieces ρ c P A val →
  18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → PartCm (recOf P val c) ρ x₀
def BoundInM : Prop := ∃ (c : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : ValQ → ℤ), IsPiecesB c P A val ∧
  PartCm (recOf P val c) (1 / Real.sqrt 2) (x₀Of c)
end GeneralPieces.Tied


