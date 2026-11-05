-- Prove2me | Definitions.Def_CountKSatRate_Defs
-- name    : CountKSatRate_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:06:34.711443+00:00
-- url     : https://prove2.me/theorems/49ccf036-e18a-4099-bc16-88f7a8098e8c
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Defs
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_PaddedDescent_F_Prog
import Definitions.Def_PaddedDescent_Reduce
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace CountKSatRate
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open WidthK (theta bsum leafC)
def roundS {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) : List σ × ℕ → List σ × ℕ
  | ([], c) => ([], c)
  | (s :: r, c) =>
    match step s with
    | none => (r, c + val s)
    | some (l, h) => (l :: h :: r, c)
def walkS (k : ℕ) (pad : U) (τ : ℕ) (val : CNode → ℕ) (r : CNode) : ℕ :=
  (pad.foldl (fun st _ => cap pad ([], 0) (roundS (stepC (theta τ) k) val st)) (cap pad ([], 0) ([r], 0))).2
def sideU (X : PFml) : PFml := (X.filter fun C => C.length == 1).dedup
def leafM (x : CNode) : Fml := sideU x.2 ++ x.1
def nK (k : ℕ) (x : List Bool) : ℕ := (decU k x).1.length
def bruteN (k : ℕ) (p : List Bool × U) : ℕ := ((rng p.2 (2 ^ nK k p.1)).filter fun y => satAt (decU k p.1).2 y).length
def padMW (e : List Bool → ℕ) (B : List Bool × List Unit → List Bool) : Stepped (List Bool) (List Bool) where
  σ := (List Bool × List Unit) ⊕ List Bool
  init x := .inl (x, [()])
  step s := s.elim (fun p => bif decide (e p.1 ≤ Nat.log2 p.2.length) then .inr (B p) else .inl (p.1, p.2 ++ p.2))
    fun w => .inr w
  out s := s.elim (fun _ => none) fun w => some w
def stackLenC (k τ n m : ℕ) : ℕ :=
  (bsum τ k * n + 1) * (2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8) + 3 * n + 16
end CountKSatRate


