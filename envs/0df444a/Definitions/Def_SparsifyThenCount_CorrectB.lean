-- Prove2me | Definitions.Def_SparsifyThenCount_CorrectB
-- name    : SparsifyThenCount_CorrectB
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:33:10.031021+00:00
-- url     : https://prove2.me/theorems/df7a54ac-1117-48b1-8bba-112efcca534c
-- title:
--   Correct B
-- statement:
--   Definitions and structural lemmas for Correct B, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CorrectB.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_VariableBound_Top_CorrectB
set_option autoImplicit false
section
section
@[expose] section
namespace SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.CorrectB
end SparsifyThenCount


