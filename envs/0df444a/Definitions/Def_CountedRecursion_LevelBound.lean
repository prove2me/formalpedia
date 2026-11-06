-- Prove2me | Definitions.Def_CountedRecursion_LevelBound
-- name    : CountedRecursion_LevelBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:12:22.341073+00:00
-- url     : https://prove2.me/theorems/1cd7bc54-8faf-4398-8343-8ec1b795d896
-- title:
--   Level Bound
-- statement:
--   Definitions and structural lemmas for Level Bound, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
end ExplicitCost


