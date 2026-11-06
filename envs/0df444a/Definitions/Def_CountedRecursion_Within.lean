-- Prove2me | Definitions.Def_CountedRecursion_Within
-- name    : CountedRecursion_Within
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:34:07.374273+00:00
-- url     : https://prove2.me/theorems/11bb555a-9c6d-4d4e-9cb1-0e16ed6a4258
-- title:
--   Within
-- statement:
--   Definitions and structural lemmas for Within, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Groundwork QueryMachines Finset
variable {Q Q' A A' α α₁ α₂ β γ : Type}
end ExplicitCost


