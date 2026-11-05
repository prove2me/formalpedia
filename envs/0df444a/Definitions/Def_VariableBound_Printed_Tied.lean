-- Prove2me | Definitions.Def_VariableBound_Printed_Tied
-- name    : VariableBound_Printed_Tied
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:27:40.671338+00:00
-- url     : https://prove2.me/theorems/66136722-7a7c-4ed2-9605-ee4ce1e1ff68
-- title:
--   Tied
-- statement:
--   Definitions and structural lemmas for Tied, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/Tied.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_TiedDefs
import Definitions.Def_UniformInK_Top_End
import Definitions.Def_ClauseBound_Both_End
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End UniformInK UniformInK.End VariableBound.Decide
end VariableBound


