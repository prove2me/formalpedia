-- Prove2me | Definitions.Def_GeneralPieces_GenF_Main
-- name    : GeneralPieces_GenF_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:14:19.968132+00:00
-- url     : https://prove2.me/theorems/4ea02fef-6a81-4308-9949-ac307240cd92
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Commute
import Definitions.Def_GeneralPieces_GenF_Normal
import Definitions.Def_GeneralPieces_GenF_YMain
import Definitions.Def_GeneralPieces_GenF_Assemble
import Definitions.Def_GeneralPieces_Series_LemmaQ
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.GenF
end GeneralPieces.GenF
namespace GeneralPieces.Series
open ClauseBound.Boson Finset
variable {A : FA} {b : List ℕ}
end GeneralPieces.Series


