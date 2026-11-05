-- Prove2me | Definitions.Def_PaddedDescent_F_Fuel
-- name    : PaddedDescent_F_Fuel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:46:02.903207+00:00
-- url     : https://prove2.me/theorems/fc15c31e-11f5-4bdc-a70f-7fe8703eaf17
-- title:
--   Fuel
-- statement:
--   Definitions and structural lemmas for Fuel, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Fuel.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace PaddedDescent.F
open Groundwork
abbrev U := List Unit
def rng (pad : U) (q : ℕ) : List ℕ := List.range (min q pad.length)
def sumF (N : ℕ) (pad : U) (f : ℕ → ℤ) : ℤ :=
  (List.range (min N pad.length)).foldl (fun acc y => acc + f y) 0
def prodL (n : ℕ) (f : ℕ → ℤ) : ℤ := (List.range n).foldl (fun acc y => acc * f y) 1
def cap {γ : Type} [Enc γ] (pad : U) (d x : γ) : γ := if len x ≤ pad.length then x else d
class Meas (α : Type) [Enc α] : Prop where
  poly : PolyT (fun x : α => len x)
end PaddedDescent.F


