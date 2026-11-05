-- Prove2me | Definitions.Def_ClauseBound_Inst_Half
-- name    : ClauseBound_Inst_Half
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:38:30.424774+00:00
-- url     : https://prove2.me/theorems/cf6f4508-ec6b-4a97-9808-d30907a581c8
-- title:
--   Half
-- statement:
--   Definitions and structural lemmas for Half, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/Half.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfPart
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Alg_Prog
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
def sOf (h i : ℕ) : ℤ := ((min i (4 * h) : ℕ) : ℤ) - 2 * h
def wOf (tr : Bool) (h : ℕ) (s : ℤ) (j : ℕ) : ℤ := bif tr then 2 * h - s - j else s + j
def labs (T : PT) (tr : Bool) (h : ℕ) (s : ℤ) : List (ℕ × List ℕ) :=
  (List.range (2 * h + 1)).flatMap fun j =>
    if 0 ≤ wOf tr h s j then (T.getD (wOf tr h s j).toNat []).map fun τ => (j, τ) else []
def encF (T : PT) (h : ℕ) (x : List Bool) : List ℕ := (T.getD h []).getD (ofWord x) []
def partT (pad : U) (tr top : Bool) (h : ℕ) (s : ℤ) (T : PT) (a b θ : List Bool) : ℤ :=
  ((labs T tr h s)[ofWord θ]?).elim 0 fun p =>
    bif top then
      (bif tr then topF pad (4 * h) T.flatten h (encF T h a) p.1 (s - h + p.1) (encF T h b) p.2
       else topF pad (4 * h) T.flatten h (encF T h a) p.1 (s - h + p.1) p.2 (encF T h b))
    else
      (bif tr then botF pad (4 * h) T.flatten h (encF T h b) (h - s - p.1) p.2 (encF T h a)
       else botF pad (4 * h) T.flatten h (encF T h b) (h - s - p.1) (encF T h a) p.2)
def partH (c₀ : ℕ) (top : Bool) (q : PQ) : ℤ :=
  partT q.1.1 q.1.2 top (hF c₀ q.2.2.1.length) (sOf (hF c₀ q.2.2.1.length) q.2.1.2) (allTabF q.1.1 (4 * hF c₀ q.2.2.1.length))
    q.2.2.1 q.2.2.2.1 q.2.2.2.2
def deltaF (h : ℕ) : ℕ := (pTab (4 * h)).sum
def padLen (h : ℕ) : ℕ := 2 ^ 10 * (h + 2) ^ 4 * (deltaF h + 1) ^ 2
def halfF (c₀ c : ℕ) : PiecesF where
  cnt _ lam := 4 * hF c₀ lam + 1
  d _ lam := factN (hF c₀ lam)
  cap tr _ lam i := min (2 * c * lam)
    (Nat.clog 2 (bif tr then RcolF (hF c₀ lam) (sOf (hF c₀ lam) i) else RrowF (hF c₀ lam) (sOf (hF c₀ lam) i)))
  top := partH c₀ true
  bot := partH c₀ false
  need _ lam := c * lam
  bits _ lam := (2 * lam) ^ c
  m := c
end ClauseBound.Inst.Half


