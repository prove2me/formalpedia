-- Prove2me | Definitions.Def_VariableBound_StepParity
-- name    : VariableBound_StepParity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:26:00.148199+00:00
-- url     : https://prove2.me/theorems/ddd7aa77-96db-4a83-a520-34edf1f439e7
-- title:
--   Step Parity
-- statement:
--   Definitions and structural lemmas for Step Parity, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepParity.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.StepParity
open Finset ParityChecks AppVariables
variable {X E : Type} [DecidableEq E]
variable [Fintype X]
end VariableBound.StepParity
namespace VariableBound
open Finset ParityChecks AppVariables StepParity
end VariableBound


