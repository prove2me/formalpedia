-- Prove2me | Definitions.Def_Consequences_Defs
-- name    : Consequences_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:43:55.500203+00:00
-- url     : https://prove2.me/theorems/240fd543-409e-45dd-ab75-624d81a338c7
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_Complement_Defs
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Eight_Cor_NSETHDefs
import Definitions.Def_CircuitLowerBoundStatement
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Alg_Machine
set_option autoImplicit false
section
section
namespace Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping SplitCount SplitSat SizeCircuit Complement
def CountsGraph (Ms : StepMachine (List Bool) ℕ) (f : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → ℕ) (δ : ℝ) (c : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n → ∃ T : ℕ, Ms.Runs (codeWith G s) T (c * (n + 2) ^ c) (f n G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)
end Consequences


