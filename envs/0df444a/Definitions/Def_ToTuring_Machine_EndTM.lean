-- Prove2me | Definitions.Def_ToTuring_Machine_EndTM
-- name    : ToTuring_Machine_EndTM
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:47:00.649702+00:00
-- url     : https://prove2.me/theorems/b33255a4-f5d8-4446-89fe-c0041c7a1e1b
-- title:
--   End TM
-- statement:
--   Definitions and structural lemmas for End TM, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/EndTM.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_StepMachines_Prog_Decode
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
set_option autoImplicit false
section
namespace Groundwork
open Sat3 Turing
open scoped NNReal
end Groundwork


