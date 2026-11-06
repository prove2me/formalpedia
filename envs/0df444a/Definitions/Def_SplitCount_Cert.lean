-- Prove2me | Definitions.Def_SplitCount_Cert
-- name    : SplitCount_Cert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:30:09.122331+00:00
-- url     : https://prove2.me/theorems/c580a6c5-9e5b-4657-98ab-533f5a92eb46
-- title:
--   Cert
-- statement:
--   Definitions and structural lemmas for Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Cert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_Occ_Main
import Definitions.Def_CountKSat_Walk
import Definitions.Def_CountKSat_Poly
import Definitions.Def_ToTuring_Poly_Sat
set_option autoImplicit false
section
section
@[expose] section
namespace SplitCount
open Groundwork Groundwork.Prog Groundwork.Stepped Paper CountKSat Eight.Width Occ
end SplitCount


