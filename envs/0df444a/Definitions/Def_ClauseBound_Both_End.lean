-- Prove2me | Definitions.Def_ClauseBound_Both_End
-- name    : ClauseBound_Both_End
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:17:44.266824+00:00
-- url     : https://prove2.me/theorems/1f69574c-59aa-412f-8248-d72ed38b9d3a
-- title:
--   End
-- statement:
--   Definitions and structural lemmas for End, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Both/End.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Both_Defs
import Definitions.Def_ClauseBound_Alg_End
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Both.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
end ClauseBound.Both.End


