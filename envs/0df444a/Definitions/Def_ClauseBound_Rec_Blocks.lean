-- Prove2me | Definitions.Def_ClauseBound_Rec_Blocks
-- name    : ClauseBound_Rec_Blocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:28:48.212226+00:00
-- url     : https://prove2.me/theorems/92d828e1-5340-41ff-85ae-b10853402345
-- title:
--   Blocks
-- statement:
--   Definitions and structural lemmas for Blocks, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Blocks.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Defs
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Rec
open Finset Polynomial Pieces
variable {n h : ℕ}
theorem le_mul_nblk (n : ℕ) (hh : 1 ≤ h) : n ≤ h * nblk n h := by
  unfold nblk
  have h1 := Nat.div_add_mod (n + h - 1) h
  have h2 := Nat.mod_lt (n + h - 1) hh
  omega
theorem div_lt_nblk (hh : 1 ≤ h) (k : Fin n) : k.val / h < nblk n h := by
  rw [Nat.div_lt_iff_lt_mul hh]
  have h1 := le_mul_nblk n hh
  have h2 := k.isLt
  rw [Nat.mul_comm] at h1
  omega
theorem family_congr (F : ∀ b : Fin (nblk n h), BLab n h b) (k : Fin n) {b b' : Fin (nblk n h)} (hk : k.val / h = b.val)
    (hk' : k.val / h = b'.val) : F b ⟨k, hk⟩ = F b' ⟨k, hk'⟩ := by
  obtain rfl : b = b' := Fin.ext (hk.symm.trans hk')
  rfl
noncomputable def split (hh : 1 ≤ h) : Lab n ≃ ∀ b : Fin (nblk n h), BLab n h b where
  toFun β _ k := β k.1
  invFun F k := F ⟨k.val / h, div_lt_nblk hh k⟩ ⟨k, rfl⟩
  left_inv _ := rfl
  right_inv F := by
    funext b k
    exact family_congr F k.1 rfl k.2
end ClauseBound.Rec


