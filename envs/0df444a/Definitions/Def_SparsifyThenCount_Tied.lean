-- Prove2me | Definitions.Def_SparsifyThenCount_Tied
-- name    : SparsifyThenCount_Tied
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:33:36.356089+00:00
-- url     : https://prove2.me/theorems/49648bfd-db3e-4e87-8682-3bdb05e422f8
-- title:
--   Tied
-- statement:
--   Definitions and structural lemmas for Tied, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/Tied.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_UniformInK_Top_End
import Definitions.Def_ClauseBound_Both_End
set_option autoImplicit false
section
section
@[expose] section
namespace SparsifyThenCount
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End UniformInK UniformInK.End VariableBound VariableBound.Decide
end SparsifyThenCount


