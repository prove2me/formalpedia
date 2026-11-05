-- Prove2me | Definitions.Def_VariableBound_Top_ArithPlan
-- name    : VariableBound_Top_ArithPlan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:24:49.092776+00:00
-- url     : https://prove2.me/theorems/225df023-8f4c-4294-a312-469ba19cd3af
-- title:
--   Arith Plan
-- statement:
--   Definitions and structural lemmas for Arith Plan, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithPlan.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Mathlib.Tactic.SplitIfs
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.Mark CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound.Net
end VariableBound


