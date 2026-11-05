-- Prove2me | Definitions.Def_Eight_SecCrossing_Cert
-- name    : Eight_SecCrossing_Cert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:27:44.350753+00:00
-- url     : https://prove2.me/theorems/77ba6b3e-8f19-41b6-9824-82098397a7a3
-- title:
--   Sec Crossing Cert
-- statement:
--   Definitions and structural lemmas for Sec Crossing Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Eight_SecCrossing_MulOut
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
set_option autoImplicit false
section
section
@[expose] section
namespace Eight
open Groundwork PaddedDescent.F ClauseBound.Alg SingleBitPieces.SecCrossing_PolyA
namespace SecCrossing_Cert
variable {α : Type} [Enc α]
abbrev Arg : Type := Bool × ℕ × List Bool × List Bool × List Bool
end SecCrossing_Cert
open SecCrossing_Cert
end Eight


