-- Prove2me | Definitions.Def_StepMachines_Prog_BruteE
-- name    : StepMachines_Prog_BruteE
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:23:53.621218+00:00
-- url     : https://prove2.me/theorems/d54e2bcc-3607-4a88-a9ae-b036af03f3f8
-- title:
--   Brute E
-- statement:
--   Definitions and structural lemmas for Brute E, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/BruteE.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
set_option autoImplicit false
section
namespace Groundwork.Prog
open Finset Stepped
@[expose] public def nilC {C : Type} (_ : C) : List Bool := []
@[expose] public def bruteE (K : ℕ) : Evaluator := ⟨fun lam R => brute K lam nilC R⟩
end Groundwork.Prog


