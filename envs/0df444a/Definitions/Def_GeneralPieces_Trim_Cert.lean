-- Prove2me | Definitions.Def_GeneralPieces_Trim_Cert
-- name    : GeneralPieces_Trim_Cert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:24:13.62405+00:00
-- url     : https://prove2.me/theorems/3ce57664-53a8-4561-a48c-26403c58ba92
-- title:
--   Cert
-- statement:
--   Definitions and structural lemmas for Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Cert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Trim_Prog
import Definitions.Def_PaddedDescent_F_FuelCert
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen
namespace Trim
variable {α : Type} [Enc α] {P : PiecesF}
end Trim
open Trim
end GeneralPieces


