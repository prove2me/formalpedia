-- Prove2me | Definitions.Def_Coding_OccTests
-- name    : Coding_OccTests
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:12:01.439202+00:00
-- url     : https://prove2.me/theorems/65b0d1ac-4b5b-4802-8f5c-031cac571aed
-- title:
--   Occ Tests
-- statement:
--   Definitions and structural lemmas for Occ Tests, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccMore
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_SecProof_Network
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight
variable {Φ : Fml}
@[expose] def occOfSlot {m : ℕ} (p : Slot 1 m 3) : ℕ × ℕ := (p.2.1.val, p.2.2.val)
end Coding


