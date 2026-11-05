-- Prove2me | Definitions.Def_ThmVariables_Bound
-- name    : ThmVariables_Bound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:49:48.468864+00:00
-- url     : https://prove2.me/theorems/2999ad8d-3c8a-4bbb-ba99-126373011435
-- title:
--   Bound
-- statement:
--   Definitions and structural lemmas for Bound, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/Bound.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false
section
section
@[expose] section
namespace ThmVariables
open Turing CliqueLevels MainTheoremForms VariableBound.Paper
open Sat3 (CNF)
variable {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}
end ThmVariables


