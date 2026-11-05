-- Prove2me | Definitions.Def_CircuitLowerBound_ENP_Round
-- name    : CircuitLowerBound_ENP_Round
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:43:30.570619+00:00
-- url     : https://prove2.me/theorems/9aeb6649-7de8-401f-b837-b3bacc459ca5
-- title:
--   Round
-- statement:
--   Definitions and structural lemmas for Round, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_takeWhile
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.takeWhile


set_option autoImplicit false
section
section
namespace CircuitLowerBound
open ENP Groundwork
def mL (w : List Bool) : List ℕ := (List.range w.length).takeWhile fun i => w.getD (2 * i) false
def mU (w : List Bool) : List Unit := (mL w).map fun _ => ()
def xW (w : List Bool) : List Bool := (mL w).map fun i => w.getD (2 * i + 1) false
def aW (w : List Bool) : List Bool := w.drop (2 * (mL w).length + 1)
def eW (w : List Bool) : ℕ := 2 * (mL w).length + 4
def PhiF (G : (MCode × List Unit × ℕ) × List Unit → Cnf) (fb : List Unit → Bool) (u pad : List Unit) : Cnf :=
  bif decide (pos u.length < top (nu u.length)) then
    (bif decide (Fits (codeOf (nu u.length)) u.length (next u.length)) then G ((codeOf (nu u.length), u, next u.length), pad) else [])
  else bif decide (pos u.length = top (nu u.length)) then (bif fb u then [[]] else []) else []
def encF (pad : List Unit) (φ : Cnf) : List Bool :=
  φ.flatMap (fun C => C.flatMap (fun l => true :: ((pad.take l.1).map (fun _ => true) ++ [false, l.2])) ++ [false, true]) ++ [false, false]
def roundF (G : (MCode × List Unit × ℕ) × List Unit → Cnf) (fb : List Unit → Bool) (p : List Bool × List Unit) : List Bool :=
  bif decide ((aW p.1).length ≤ ofWord (xW p.1)) then
    true :: encF p.2 (PhiF G fb (mU p.1) p.2 ++ units ((aW p.1).map (fun b => !b) ++ [false]))
  else [false, !(aW p.1).getD (ofWord (xW p.1)) false]
namespace Round
variable {G : (MCode × List Unit × ℕ) × List Unit → Cnf} {fb : List Unit → Bool}
section Cert
variable {α : Type} [Enc α]
end Cert
end Round
end CircuitLowerBound


