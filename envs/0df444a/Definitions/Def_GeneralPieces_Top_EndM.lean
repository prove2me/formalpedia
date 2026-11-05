-- Prove2me | Definitions.Def_GeneralPieces_Top_EndM
-- name    : GeneralPieces_Top_EndM
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:50:54.931442+00:00
-- url     : https://prove2.me/theorems/5087a6e9-92a7-40a4-809f-430665bdbf65
-- title:
--   End M
-- statement:
--   Definitions and structural lemmas for End M, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Top/EndM.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_Defs
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_InOut
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Top
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat ClauseBound.Alg ClauseBound.Alg.End
end GeneralPieces.Top


