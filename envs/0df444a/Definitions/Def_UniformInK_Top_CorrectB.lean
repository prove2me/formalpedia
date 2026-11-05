-- Prove2me | Definitions.Def_UniformInK_Top_CorrectB
-- name    : UniformInK_Top_CorrectB
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:19:50.494195+00:00
-- url     : https://prove2.me/theorems/8605b554-7226-4bb4-b705-a17c15be013b
-- title:
--   Correct B
-- statement:
--   Definitions and structural lemmas for Correct B, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/CorrectB.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
set_option autoImplicit false
section
section
@[expose] section
namespace UniformInK.CorrectB
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
end UniformInK.CorrectB
namespace UniformInK
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK.CorrectB
end UniformInK


