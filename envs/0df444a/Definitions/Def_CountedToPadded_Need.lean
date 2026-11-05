-- Prove2me | Definitions.Def_CountedToPadded_Need
-- name    : CountedToPadded_Need
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:35:15.250205+00:00
-- url     : https://prove2.me/theorems/dbbb844a-6bb2-4c1d-a7c3-64e67be453ab
-- title:
--   Need
-- statement:
--   Definitions and structural lemmas for Need, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Need.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
section
section
@[expose] section
namespace QueryMachines.Bridge.Proof
open Groundwork PaddedDescent.F Printed CliqueLevels
end QueryMachines.Bridge.Proof
namespace QueryMachines.Bridge
open Groundwork PaddedDescent.F Printed CliqueLevels Proof
end QueryMachines.Bridge


