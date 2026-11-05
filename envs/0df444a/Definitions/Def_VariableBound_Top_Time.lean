-- Prove2me | Definitions.Def_VariableBound_Top_Time
-- name    : VariableBound_Top_Time
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:26:00.364293+00:00
-- url     : https://prove2.me/theorems/7535af5a-1db6-4a7c-b18d-4252bb565943
-- title:
--   Time
-- statement:
--   Definitions and structural lemmas for Time, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/Time.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_ClauseBound_TopN_End
import Definitions.Def_ClauseBound_Alg_End
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End UniformInK
end VariableBound


