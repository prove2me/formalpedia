-- Prove2me | Definitions.Def_GeneralPieces_Tied_Bound
-- name    : GeneralPieces_Tied_Bound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:35:41.840031+00:00
-- url     : https://prove2.me/theorems/277f982e-5000-4265-b244-8ba5b6a80ae6
-- title:
--   Bound
-- statement:
--   Definitions and structural lemmas for Bound, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Tied/Bound.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_BoundDefs
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_GeneralPieces_Half_Main
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half GeneralPieces.Half
end GeneralPieces


