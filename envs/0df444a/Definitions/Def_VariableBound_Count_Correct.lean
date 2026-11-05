-- Prove2me | Definitions.Def_VariableBound_Count_Correct
-- name    : VariableBound_Count_Correct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:10:01.236194+00:00
-- url     : https://prove2.me/theorems/e23db7a2-5614-43ee-979a-dc4387976051
-- title:
--   Correct
-- statement:
--   Definitions and structural lemmas for Correct, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset
section
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
end
end VariableBound.Count
namespace VariableBound
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset
end VariableBound


