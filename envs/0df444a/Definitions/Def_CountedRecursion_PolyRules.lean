-- Prove2me | Definitions.Def_CountedRecursion_PolyRules
-- name    : CountedRecursion_PolyRules
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:32:54.092946+00:00
-- url     : https://prove2.me/theorems/b272cbbb-9abd-4fc0-ae92-26110f5bb167
-- title:
--   Poly Rules
-- statement:
--   Definitions and structural lemmas for Poly Rules, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Groundwork QueryMachines QueryMachines.QueryMachine Printed
variable {Q Q' A A' C α α₁ α₂ β γ : Type} [Enc Q] [Enc Q'] [Enc A] [Enc A'] [Enc α] [Enc α₁] [Enc α₂] [Enc β] [Enc γ]
end ExplicitCost


