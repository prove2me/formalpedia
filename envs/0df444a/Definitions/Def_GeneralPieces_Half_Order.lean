-- Prove2me | Definitions.Def_GeneralPieces_Half_Order
-- name    : GeneralPieces_Half_Order
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:47:00.385905+00:00
-- url     : https://prove2.me/theorems/65dad9ff-624e-4044-a2bb-41bd35e64feb
-- title:
--   Order
-- statement:
--   Definitions and structural lemmas for Order, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_List
import Definitions.Def_ClauseBound_Inst_HalfEnc
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Half
open AppHalfPieces Finset ClauseBound.Part GeneralPieces.Ring Groundwork ClauseBound.Alg ClauseBound.Inst.Half
end GeneralPieces.Half


