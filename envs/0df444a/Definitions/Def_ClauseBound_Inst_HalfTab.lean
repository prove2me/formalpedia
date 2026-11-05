-- Prove2me | Definitions.Def_ClauseBound_Inst_HalfTab
-- name    : ClauseBound_Inst_HalfTab
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:32:25.86278+00:00
-- url     : https://prove2.me/theorems/996f15ac-364e-402e-a4f7-deae51c74f63
-- title:
--   Half Tab
-- statement:
--   Definitions and structural lemmas for Half Tab, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTab.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_RecArith
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Boson_KF
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Inst.Rec
def betF (W n : ℕ) (r : ℤ) : ℤ := if r = 0 then 0 else chooseZ (r - 1) (min n W - 1)
def tab (flat : List (List ℕ)) (f : List ℕ → List ℕ → ℤ) : List ℤ := flat.flatMap fun π => flat.map fun σ => f π σ
def lookT (flat : List (List ℕ)) (T : List ℤ) (π σ : List ℕ) : ℤ := T.getD (flat.idxOf π * flat.length + flat.idxOf σ) 0
def nopE (W n : ℕ) (flat : List (List ℕ)) (T : List ℤ) (π σ : List ℕ) : ℤ :=
  (π.dedup.map fun l : ℕ => betF W n (l : ℤ) * lookT flat T (π.erase l) σ).sum +
    (σ.dedup.map fun k : ℕ => betF W n (-(k : ℤ)) * ((k : ℤ) * (σ.count k : ℤ) * lookT flat T π (σ.erase k))).sum
def oneT (flat : List (List ℕ)) : List ℤ := tab flat fun π σ => if π = σ then 1 else 0
def tabOp (pad : U) (W : ℕ) (flat : List (List ℕ)) (a : List ℕ) : List ℤ :=
  a.reverse.foldl (fun T n => cap pad [] (tab flat (nopE W n flat T))) (cap pad [] (oneT flat))
def kfInit (h : ℕ) (flat : List (List ℕ)) : List (List ℤ) :=
  (List.range (h + 1)).map fun w => if w = 0 then oneT flat else tab flat fun _ _ => 0
def kfStep (W h n : ℕ) (flat : List (List ℕ)) (S : List (List ℤ)) : List (List ℤ) :=
  (List.range (h + 1)).map fun w => tab flat fun π σ =>
    sumR (min n W) fun j =>
      if j + 1 ≤ w then sgnZ ((n - 1 : ℕ) : ℤ) * chooseZ (n : ℤ) (j + 1) * nopE W (j + 1) flat (S.getD (w - (j + 1)) []) π σ else 0
def tabKF (pad : U) (W : ℕ) (flat : List (List ℕ)) (h : ℕ) (μ : List ℕ) : List (List ℤ) :=
  μ.reverse.foldl (fun S n => cap pad [] (kfStep W h n flat S)) (cap pad [] (kfInit h flat))
def zzF (ν : List ℕ) : ℕ := (ν.dedup.map fun k => ((k ^ ν.count k * factN (ν.count k) : ℕ) : ℤ)).prod.natAbs
def topF (pad : U) (W : ℕ) (flat : List (List ℕ)) (h : ℕ) (μx : List ℕ) (i : ℕ) (r : ℤ) (π σ : List ℕ) : ℤ :=
  if r = (π.sum : ℤ) - σ.sum then
    sgnZ i * sumR (h + 1) fun w => chooseZ ((w : ℤ) + h) i * lookT flat ((tabKF pad W flat h μx).getD w []) π σ
  else 0
def botF (pad : U) (W : ℕ) (flat : List (List ℕ)) (h : ℕ) (μv : List ℕ) (r : ℤ) (π σ : List ℕ) : ℤ :=
  if r = (π.sum : ℤ) - σ.sum then ((factN h / zzF μv : ℕ) : ℤ) * lookT flat (tabOp pad W flat μv) π σ else 0
structure FlatOK (W : ℕ) (flat : List (List ℕ)) : Prop where
  inj : ∀ π ∈ flat, ∀ σ ∈ flat, (π : Multiset ℕ) = σ → π = σ
  erase : ∀ π ∈ flat, ∀ l ∈ π, π.erase l ∈ flat
  sum_le : ∀ π ∈ flat, π.sum ≤ W
def Rep (flat : List (List ℕ)) (T : List ℤ) (F : ℤ → ClauseBound.Boson.Ker) : Prop :=
  ∀ π ∈ flat, ∀ σ ∈ flat, lookT flat T π σ = F ((π.sum : ℤ) - σ.sum) π σ
def padOp (W Δ L : ℕ) : ℕ := Δ ^ 2 * (3 * ((4 * W + 1) * L) + 10) + 2
def padKF (W Δ h s L : ℕ) : ℕ := (h + 1) * (Δ ^ 2 * (3 * (s + (4 * W + 1) * L)  + 10) + 4) + 2
end ClauseBound.Inst.Half


