-- Prove2me | Definitions.Def_VariableBound_Top_CorrectB
-- name    : VariableBound_Top_CorrectB
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:24:52.067596+00:00
-- url     : https://prove2.me/theorems/a9db775c-38f6-4916-b25a-5c3bf8f3d21b
-- title:
--   Correct B
-- statement:
--   Definitions and structural lemmas for Correct B, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/CorrectB.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.CorrectB
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK
end VariableBound.CorrectB
namespace VariableBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound.CorrectB
end VariableBound


