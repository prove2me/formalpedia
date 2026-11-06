-- Prove2me | Definitions.Def_SplitSat_Cert
-- name    : SplitSat_Cert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:25:37.898143+00:00
-- url     : https://prove2.me/theorems/ac832649-b02a-4408-a84c-104ba387c6c1
-- title:
--   Cert
-- statement:
--   Definitions and structural lemmas for Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Cert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_CountKSat_InOut
set_option autoImplicit false
section
section
@[expose] section
namespace SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog UniformInK Paper CountKSat Eight.Width
end SplitSat


