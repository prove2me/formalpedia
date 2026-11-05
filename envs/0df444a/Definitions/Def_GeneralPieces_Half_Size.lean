-- Prove2me | Definitions.Def_GeneralPieces_Half_Size
-- name    : GeneralPieces_Half_Size
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:12:53.56421+00:00
-- url     : https://prove2.me/theorems/de184ce8-8be1-45a4-9037-b495e1f9a3da
-- title:
--   Size
-- statement:
--   Definitions and structural lemmas for Size, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Size.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_GeneralPieces_Half_Order
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Half
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes ClauseBound.Inst.Half
end GeneralPieces.Half


