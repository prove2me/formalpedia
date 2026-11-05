-- Prove2me | Definitions.Def_GeneralPieces_Ring_Op
-- name    : GeneralPieces_Ring_Op
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:21:11.910247+00:00
-- url     : https://prove2.me/theorems/19a436c5-366f-46f4-aefd-6ba44c11613f
-- title:
--   Op
-- statement:
--   Definitions and structural lemmas for Op, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_op_add_left
import Theorems.Thm_GeneralPieces_Ring_op_smul_left

set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
@[expose] noncomputable def opLeft (r : ℤ) (f : V) : V →ₗ[ℚ] V where
  toFun := fun a => op a r f
  map_add' := fun a a' => op_add_left a a' r f
  map_smul' := fun q a => op_smul_left a r q f
end GeneralPieces.Ring
namespace GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
end GeneralPieces


