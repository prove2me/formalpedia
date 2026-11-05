-- Prove2me | Definitions.Def_GeneralPieces_Ring_Sizes
-- name    : GeneralPieces_Ring_Sizes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:21:51.423916+00:00
-- url     : https://prove2.me/theorems/6a4de411-242e-452a-aa38-653534474a34
-- title:
--   Sizes
-- statement:
--   Definitions and structural lemmas for Sizes, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
@[expose] def Delta (h : ℕ) : ℕ := ∑ E ∈ range (4 * h + 1), Partitions.p E
@[expose] noncomputable def l1 (a : V) : ℚ := ∑ m ∈ a.support, |coeff m a|
end GeneralPieces.Sizes


