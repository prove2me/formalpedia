-- Prove2me | Definitions.Def_ThmVariables_PartA
-- name    : ThmVariables_PartA
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:53:32.502797+00:00
-- url     : https://prove2.me/theorems/e1575001-0c04-465d-a4a1-cee5ae5089a2
-- title:
--   Part A
-- statement:
--   Definitions and structural lemmas for Part A, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/PartA.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_ThmVariables_Bound
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
section
section
@[expose] section
namespace ThmVariables
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms
open Sat3 (CNF)
end ThmVariables


