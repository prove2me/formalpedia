-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_EndOL
-- name    : ClauseBound_ParityChecks_EndOL
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:07:38.484342+00:00
-- url     : https://prove2.me/theorems/b802c106-972c-4af1-8fc5-cb8fac12f3b4
-- title:
--   End OL
-- statement:
--   Definitions and structural lemmas for End OL, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/EndOL.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_End
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_WidthK_Decode
import Definitions.Def_CountKSat_InOut
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks.EndOL
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End ClauseBound.ParityChecks
end ClauseBound.ParityChecks.EndOL


