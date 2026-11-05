-- Prove2me | Definitions.Def_VariableBound_Net_StepCost
-- name    : VariableBound_Net_StepCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:49:25.927415+00:00
-- url     : https://prove2.me/theorems/1dde6d4f-a1e7-4c7b-b366-e14c899bce36
-- title:
--   Step Cost
-- statement:
--   Definitions and structural lemmas for Step Cost, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/StepCost.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_TopNet
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
section
section
namespace VariableBound.Net.StepCost
open Groundwork ClauseBound.Alg
end VariableBound.Net.StepCost


