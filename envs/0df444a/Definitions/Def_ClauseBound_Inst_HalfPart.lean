-- Prove2me | Definitions.Def_ClauseBound_Inst_HalfPart
-- name    : ClauseBound_Inst_HalfPart
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:47:26.961851+00:00
-- url     : https://prove2.me/theorems/013ecddb-1c59-42e7-a029-5bd9c1a46fe2
-- title:
--   Half Part
-- statement:
--   Definitions and structural lemmas for Half Part, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
namespace ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset
def nextP (T : List ℕ) : ℕ :=
  ((List.range T.length).map fun v =>
    ((List.range (T.length / (v + 1))).map fun k => (v + 1) * T.getD (T.length - (k + 1) * (v + 1)) 0).sum).sum / T.length
def pTab (W : ℕ) : List ℕ := (List.range W).foldl (fun T _ => T ++ [nextP T]) [1]
def pzF (T : List ℕ) (E : ℤ) : ℕ := if 0 ≤ E then T.getD E.toNat 0 else 0
def hF (c₀ lam : ℕ) : ℕ :=
  ((List.range (c₀ * lam ^ 2 + 1)).find? fun E => decide (2 ≤ E) && decide (2 ^ lam ≤ (pTab (c₀ * lam ^ 2)).getD E 0)).getD 2
def RrowF (h : ℕ) (s : ℤ) : ℕ := ((List.range (2 * h + 1)).map fun i : ℕ => pzF (pTab (4 * h)) (s + i)).sum
def RcolF (h : ℕ) (s : ℤ) : ℕ := ((List.range (2 * h + 1)).map fun i : ℕ => pzF (pTab (4 * h)) (2 * h - s - i)).sum
abbrev PT : Type := List (List (List ℕ))
def initT (W : ℕ) : PT := (List.range (W + 1)).map fun E => if E = 0 then [[]] else []
def stepE (k : ℕ) (old new : PT) (E : ℕ) : PT :=
  new ++ [old.getD E [] ++ (if k ≤ E then (new.getD (E - k) []).map fun L => k :: L else [])]
def roundT (W k : ℕ) (old : PT) : PT := (List.range (W + 1)).foldl (stepE k old) []
def allTab (W : ℕ) : PT := (List.range W).foldl (fun old k => roundT W (k + 1) old) (initT W)
def roundF (pad : U) (W k : ℕ) (old : PT) : PT :=
  (List.range (W + 1)).foldl (fun new E => cap pad [] (stepE k old new E)) (cap pad [] [])
def allTabF (pad : U) (W : ℕ) : PT :=
  (List.range W).foldl (fun old k => cap pad [] (roundF pad W (k + 1) old)) (cap pad [] (initT W))
def tabK (W k : ℕ) : PT := (List.range (W + 1)).map fun E => partsLe E k
end ClauseBound.Inst.Half


