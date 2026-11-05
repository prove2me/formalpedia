-- Prove2me | Definitions.Def_Coding_OccLists
-- name    : Coding_OccLists
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:58:51.679422+00:00
-- url     : https://prove2.me/theorems/42fa1da3-51d1-4346-9215-75e2497fc6ab
-- title:
--   Occ Lists
-- statement:
--   Definitions and structural lemmas for Occ Lists, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Data.List.ProdSigma
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
@[expose] def lexLt (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)
variable {g : ℕ} {Φ : Fml}
@[expose] def place (o : ℕ × ℕ) : ℕ := o.1 * 3 + o.2
end Coding


