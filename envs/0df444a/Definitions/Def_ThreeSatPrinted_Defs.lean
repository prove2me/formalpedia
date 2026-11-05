-- Prove2me | Definitions.Def_ThreeSatPrinted_Defs
-- name    : ThreeSatPrinted_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:09:37.39495+00:00
-- url     : https://prove2.me/theorems/ed7ec271-1e91-4988-90a8-c3a8971121d5
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatPrinted/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatOnTree_Defs
import Definitions.Def_Eight_ViaGrouping_AlgDefs
set_option autoImplicit false
section
section
namespace ThreeSatPrinted
open Paper
def SATCp (ℓ τ : ℕ) : StepMachine (List Bool) Bool := ThreeSatOnTree.satC τ (Eight.ViaGrouping.COUNTp ℓ)
end ThreeSatPrinted


