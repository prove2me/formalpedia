-- Prove2me | Definitions.Def_CountedRecursion_ChainLabel
-- name    : CountedRecursion_ChainLabel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:06:04.502835+00:00
-- url     : https://prove2.me/theorems/8d4f75cc-4e24-4c2c-9e27-ca1e2abe6ce6
-- title:
--   Chain Label
-- statement:
--   Definitions and structural lemmas for Chain Label, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
end ExplicitCost


