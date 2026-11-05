-- Prove2me | Definitions.Def_Wrap_FrontEnd
-- name    : Wrap_FrontEnd
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:43:38.765004+00:00
-- url     : https://prove2.me/theorems/15fa61e1-20c0-45a4-9a9a-1a3a4fc14e0e
-- title:
--   Front End
-- statement:
--   Definitions and structural lemmas for Front End, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic.Linarith
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_takeWhile
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.takeWhile
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
namespace Wrap
open Groundwork Groundwork.Decode
def slotNat (o : Option (ℕ × Bool)) : ℕ := o.elim 0 fun l => 2 * l.1 + 1 + l.2.toNat
def addFour (d : ℕ × NCNF) : NCNF := d.2 ++ [[(d.1, true)], [(d.1 + 1, true)], [(d.1 + 2, true)], [(d.1 + 3, true)]]
def encUnary (w : List Unit) (F : NCNF) : List Bool :=
  List.replicate 3 true ++ false :: (w.map (fun _ => true) ++ false :: F.flatMap fun C => (List.range 3).flatMap fun j =>
    (List.range w.length).map (slotNat C[j]?).testBit)
def slotBits (x : List Bool) : ℕ := Nat.log2 (2 * ((x.takeWhile id).length + 4)) + 1
def frontEnd (x : List Bool) : List Bool := encUnary (List.replicate (slotBits x) ()) (addFour (dec x))
end Wrap


