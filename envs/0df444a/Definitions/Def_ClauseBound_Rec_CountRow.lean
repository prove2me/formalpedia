-- Prove2me | Definitions.Def_ClauseBound_Rec_CountRow
-- name    : ClauseBound_Rec_CountRow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:29:24.664793+00:00
-- url     : https://prove2.me/theorems/d82438a9-a3ff-4237-b353-b981f781cea1
-- title:
--   Count Row
-- statement:
--   Definitions and structural lemmas for Count Row, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Rec
open Finset Polynomial Pieces
namespace CountRow
section Product
variable {δ : ℕ} (Ω : Fin δ → Type) [∀ b, Fintype (Ω b)] [∀ b, Nonempty (Ω b)] [∀ b, DecidableEq (Ω b)] (S : ∀ b, Finset (Ω b))
end Product
variable {n h : ℕ}
def oddSet (n h : ℕ) (b : Fin (nblk n h)) : Finset (BLab n h b) := {γ | Odd #{k | γ k = (true, true)}}
noncomputable def mean (n h : ℕ) : ℝ := ∑ b, (#(oddSet n h b) : ℝ) / Fintype.card (BLab n h b)
end CountRow
open CountRow
variable {n h : ℕ}
end ClauseBound.Rec


