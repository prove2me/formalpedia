-- Prove2me | Definitions.Def_PaddedDescent_Col_Good
-- name    : PaddedDescent_Col_Good
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:51:21.208472+00:00
-- url     : https://prove2.me/theorems/6150611a-9176-4449-b69c-b317073095ad
-- title:
--   Good
-- statement:
--   Definitions and structural lemmas for Good, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Good.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Col_Colouring
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_PaddedDescent_F_Interfaces
set_option autoImplicit false
section
section
@[expose] section
namespace PaddedDescent.Col
open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F Finset
variable {C : Type}
variable {K g : ℕ} (Np : PNet C) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
end PaddedDescent.Col


