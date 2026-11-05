-- Prove2me | Definitions.Def_StepMachines_Prog_NetRun
-- name    : StepMachines_Prog_NetRun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:57:30.625764+00:00
-- url     : https://prove2.me/theorems/9fe03168-2612-4340-ba17-b2057660ce65
-- title:
--   Net Run
-- statement:
--   Definitions and structural lemmas for Net Run, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
set_option autoImplicit false
section
namespace Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
section net
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
variable [HasSize C]
end net
variable [HasSize C]
end Groundwork.Prog.NetE


