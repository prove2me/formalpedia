-- Prove2me | Definitions.Def_CountedRecursion_CountStep
-- name    : CountedRecursion_CountStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:18:46.142111+00:00
-- url     : https://prove2.me/theorems/7281d8af-08df-4798-9e32-ffb3cfbd21ac
-- title:
--   Count Step
-- statement:
--   Definitions and structural lemmas for Count Step, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CountStep.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Definitions.Def_GeneralPieces_Rec_Count
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Levels.Gen Printed QueryMachines
end ExplicitCost


