-- Prove2me | Definitions.Def_ClauseBound_TopN_End
-- name    : ClauseBound_TopN_End
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:59:56.265906+00:00
-- url     : https://prove2.me/theorems/bf7cd055-8bf1-4a05-9c20-74a2dad103ca
-- title:
--   End
-- statement:
--   Definitions and structural lemmas for End, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/End.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_WidthK_Decode
import Definitions.Def_CountKSat_InOut
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.TopN.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End
end ClauseBound.TopN.End


