-- Prove2me | Definitions.Def_StepMachines_Prog_Walk
-- name    : StepMachines_Prog_Walk
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:20:18.024139+00:00
-- url     : https://prove2.me/theorems/64171d10-3535-4d16-8779-adfa19b9de04
-- title:
--   Walk
-- statement:
--   Definitions and structural lemmas for Walk, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Walk.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
set_option autoImplicit false
section
namespace Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β τ ν : Type}
@[expose] public def guard (sel : τ → Option ν) (T : Stepped ν β) (d : β) : Stepped τ β where
  σ := Option T.σ
  init x := (sel x).map T.init
  step := Option.map T.step
  out s := match s with | none => some d | some s => T.out s
variable (step : ν → Option (ν × ν))
@[expose] public def walkNext : List ν → Option (List ν)
  | [] => none
  | s :: r => some (match step s with | none => r | some (l, h) => l :: h :: r)
@[expose] public def walkSel : List ν → Option ν
  | [] => none
  | s :: _ => match step s with | none => some s | some _ => none
@[expose] public def walk [HasSize ν] (root : α → ν) (T : Stepped ν Bool) : Stepped α Bool :=
  foldWhile (fun a => some [root a]) (walkNext step) (guard (walkSel step) T false) (fun c _ b => c || b)
    fun _ => false
@[expose] public def visits : ℕ → ν → List ν → List (List ν)
  | 0, s, r => [s :: r]
  | k + 1, s, r =>
    match step s with
    | none => [s :: r]
    | some (l, h) => (s :: r) :: (visits k l (h :: r) ++ visits k h r)
end Groundwork.Stepped


