-- Prove2me | Definitions.Def_CountedToPadded_Levels
-- name    : CountedToPadded_Levels
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:07:46.017234+00:00
-- url     : https://prove2.me/theorems/4aeb600e-27bc-4da1-9e68-085700e93a88
-- title:
--   Levels
-- statement:
--   Definitions and structural lemmas for Levels, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Levels.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Tables
import Definitions.Def_CountedToPadded_Need
import Definitions.Def_CountedToPadded_Pick
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false
section
section
@[expose] section
namespace QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Eight.SecNetworks Printed CliqueLevels
section
variable {M : QueryMachine TableQuery ℤ (U × U × U) ℤ} [QueryMachine.IsPolyQ M] {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} {num : U × U → ℕ × ℕ}
end
end QueryMachines.Bridge.Proof
namespace QueryMachines.Bridge
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Eight.SecNetworks Printed CliqueLevels Proof
end QueryMachines.Bridge
namespace CliqueLevels
open QueryMachines Printed
end CliqueLevels


