-- Prove2me | Definitions.Def_CircuitLowerBound_Alg_Parse
-- name    : CircuitLowerBound_Alg_Parse
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:09:23.086639+00:00
-- url     : https://prove2.me/theorems/17a7472d-8b20-4458-b8dc-0b56a8196338
-- title:
--   Parse
-- statement:
--   Definitions and structural lemmas for Parse, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace CircuitLowerBound
open ENP Groundwork
namespace Parse
def gateW (W : ℕ) (g : GateD) : List Bool := [g.1.1, g.1.2.1, g.1.2.2.1, g.1.2.2.2] ++ (toWord W g.2.1 ++ toWord W g.2.2)
def encC (W : ℕ) (C : List GateD) : List Bool := unary W ++ (C.map (gateW W)).flatten
def gateOfW (W : ℕ) (b : List Bool) : GateD :=
  ((b.getD 0 false, b.getD 1 false, b.getD 2 false, b.getD 3 false), ofWord ((b.drop 4).take W), ofWord (b.drop (4 + W)))
def decC (y : List Bool) : List GateD :=
  (List.range ((rest y).length / (4 + 2 * ones y))).map fun t => gateOfW (ones y) (block (4 + 2 * ones y) t (rest y))
def wfB (n : ℕ) (C : List GateD) : Bool :=
  (List.range C.length).all fun t =>
    decide ((C.getD t ((false, false, false, false), 0, 0)).2.1 < n + t) && decide ((C.getD t ((false, false, false, false), 0, 0)).2.2 < n + t)
section cert
variable {α : Type} [Enc α]
end cert
end Parse
end CircuitLowerBound


