-- Prove2me | Definitions.Def_GeneralPieces_Series_ReadOff
-- name    : GeneralPieces_Series_ReadOff
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:24:27.780132+00:00
-- url     : https://prove2.me/theorems/6458e8e1-fe07-4c37-ab6d-57b631df631e
-- title:
--   Read Off
-- statement:
--   Definitions and structural lemmas for Read Off, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/ReadOff.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
set_option autoImplicit false
section
section
namespace GeneralPieces.Series
open ClauseBound.Boson Finset
def qP (a b : List ℕ) (s : ℤ) (π σ : Multiset ℕ) : ℤ :=
  ∑ i ∈ range (a.sum + b.sum + 1), (-1) ^ i * ((a.sum + b.sum).choose i : ℤ) * mul2 a (s - b.sum + i) b (b.sum - s - i) π σ
def qM (a b : List ℕ) (s : ℤ) (π σ : Multiset ℕ) : ℤ :=
  ∑ i ∈ range (a.sum + b.sum + 1), (-1) ^ i * ((a.sum + b.sum).choose i : ℤ) * mul2 b (b.sum - s - i) a (s - b.sum + i) π σ
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
end GeneralPieces.Series


