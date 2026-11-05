-- Prove2me | Definitions.Def_VariableBound_StepChoice
-- name    : VariableBound_StepChoice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:17:16.622596+00:00
-- url     : https://prove2.me/theorems/15a669a2-9c41-4726-b574-e040fcaecc26
-- title:
--   Step Choice
-- statement:
--   Definitions and structural lemmas for Step Choice, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
end VariableBound.StepChoice
namespace VariableBound
open AppVariables Finset
end VariableBound


