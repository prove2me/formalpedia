-- Prove2me | Definitions.Def_PaddedDescent_BrutePad
-- name    : PaddedDescent_BrutePad
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:46:04.169306+00:00
-- url     : https://prove2.me/theorems/b8d4c17e-f829-4eb1-8041-3d9f2a065177
-- title:
--   Brute Pad
-- statement:
--   Definitions and structural lemmas for Brute Pad, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/BrutePad.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_ToTuring_Poly_Decode
import Batteries.Data.Nat.Lemmas
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
namespace PaddedDescent
open Groundwork Groundwork.Decode Sat3 Turing
@[expose] public def nOf (x : List Bool) : ℕ := (dec x).1
@[expose] public def satAt (ψ : NCNF) (y : ℕ) : Bool := ψ.all fun C => C.any fun l => y.testBit l.1 == l.2
@[expose] public def bruteA (p : List Bool × List Unit) : Bool := (List.range p.2.length).any fun y => satAt (dec p.1).2 y
end PaddedDescent


