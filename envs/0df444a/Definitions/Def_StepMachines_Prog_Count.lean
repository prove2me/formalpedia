-- Prove2me | Definitions.Def_StepMachines_Prog_Count
-- name    : StepMachines_Prog_Count
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:24:30.090198+00:00
-- url     : https://prove2.me/theorems/04b70d82-b497-4d86-a534-6ca8078b8b61
-- title:
--   Count
-- statement:
--   Definitions and structural lemmas for Count, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Count.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatArith
set_option autoImplicit false
section
namespace Groundwork.Prog
open Finset Groundwork.Prog.Count
@[expose] public def Fml.Sat (φ : Fml) : Prop := ∃ a : ℕ → Bool, ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2
@[expose] public def satP (g k : ℕ) : PNet Fml where
  n φ _ := mu g φ * k
  cap φ a b := capF g k φ a b
  W := Stepped.ofFun (wF g k)
  f := Stepped.ofFun (fF g k)
def S₀ (g k : ℕ) (φ : Fml) : ℕ := size φ + 2 * g + 6 * (mu g φ * k) + 8
end Groundwork.Prog


