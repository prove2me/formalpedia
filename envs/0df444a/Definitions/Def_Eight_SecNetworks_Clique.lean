-- Prove2me | Definitions.Def_Eight_SecNetworks_Clique
-- name    : Eight_SecNetworks_Clique
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:58:12.866508+00:00
-- url     : https://prove2.me/theorems/cdab0920-9677-4983-b540-3adebc144d45
-- title:
--   Sec Networks Clique
-- statement:
--   Definitions and structural lemmas for Sec Networks Clique, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Eight.SecNetworks
open Groundwork Groundwork.Prog Finset
section Procedures
open Stepped
variable {C : Type}
@[expose] def tablesOn {K : ℕ} (lam : ℕ) (W : Paper.Tables K) (w : Fin K) (z : List Bool) : ℤ :=
  W w fun w' => if w' = w then [] else copyAt lam w w' z
end Procedures
end Eight.SecNetworks


