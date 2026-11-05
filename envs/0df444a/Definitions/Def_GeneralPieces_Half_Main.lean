-- Prove2me | Definitions.Def_GeneralPieces_Half_Main
-- name    : GeneralPieces_Half_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:50:00.008003+00:00
-- url     : https://prove2.me/theorems/d96db400-d534-4f92-a7e7-782862026e66
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_Spec
import Definitions.Def_GeneralPieces_Half_Order
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Definitions.Def_ClauseBound_Inst_CertHalf
import Definitions.Def_ClauseBound_Inst_HalfEnd
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half GeneralPieces.Half
end GeneralPieces


