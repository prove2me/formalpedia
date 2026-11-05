-- Prove2me | Definitions.Def_GraphProblems_Blocks
-- name    : GraphProblems_Blocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:54:23.205581+00:00
-- url     : https://prove2.me/theorems/e9117157-cd39-4c54-855e-4f72a72f880d
-- title:
--   Blocks
-- statement:
--   Definitions and structural lemmas for Blocks, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Blocks.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
section
section
@[expose] section
namespace GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
namespace Blocks
@[expose] def Sat (f : ℕ → Bool) (φ : Fml) : Prop := ∀ C ∈ φ, ∃ l ∈ C, f l.1 = l.2
end Blocks
end GraphProblems


