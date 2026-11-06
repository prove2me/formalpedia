-- Prove2me | Definitions.Def_Sat3Graph_Host
-- name    : Sat3Graph_Host
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:42:45.005197+00:00
-- url     : https://prove2.me/theorems/1d57e1e7-8675-4a0e-912b-e6be55634642
-- title:
--   Host
-- statement:
--   Definitions and structural lemmas for Host, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_GraphProblems_Read
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Sat3Graph
open Groundwork Groundwork.Prog GraphProblems Paper SplitSat
@[expose] def DecidesColor (Ms : StepMachine (List Bool) Bool) (k : ℕ) (δ : ℝ) (c : ℕ) : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  ∃ (T : ℕ) (b : Bool), Ms.Runs (code G) T (c * (n + 2) ^ c) b ∧ (b = true ↔ G.Colorable k) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)
end Sat3Graph


