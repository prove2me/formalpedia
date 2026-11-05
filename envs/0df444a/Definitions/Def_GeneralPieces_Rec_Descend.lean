-- Prove2me | Definitions.Def_GeneralPieces_Rec_Descend
-- name    : GeneralPieces_Rec_Descend
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:59:49.121215+00:00
-- url     : https://prove2.me/theorems/e20b27d2-6ac0-4f06-ab3f-beade0b16a5d
-- title:
--   Descend
-- statement:
--   Definitions and structural lemmas for Descend, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Descend.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Alg_Descend
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists ClauseBound.Alg ClauseBound.Alg.Descend
end GeneralPieces.Descend


