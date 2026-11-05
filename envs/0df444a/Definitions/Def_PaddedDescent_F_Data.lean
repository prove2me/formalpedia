-- Prove2me | Definitions.Def_PaddedDescent_F_Data
-- name    : PaddedDescent_F_Data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:00:01.033131+00:00
-- url     : https://prove2.me/theorems/f8e986c0-de35-4c0f-bdf8-53afd5248567
-- title:
--   Data
-- statement:
--   Definitions and structural lemmas for Data, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Data.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_StepMachines_Prog_Brute
import Definitions.Def_StepMachines_Prog_Spec
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace PaddedDescent.F
open Groundwork Groundwork.Prog
abbrev Tab := List (List ℤ)
abbrev PInst := U × Tab
abbrev Lvl := U × U
def look (T : Tab) (q : IQ) : ℤ := (T.getD q.1 []).getD (ofWord q.2.flatten) 0
def instOf {K : ℕ} (T : Tab) : Inst (Fin K) (List Bool) := fun v θ => look T (v.1, List.ofFn θ)
def zval (K : ℕ) (I : PInst) : ℤ := Inst.ZW I.1.length [] (instOf (K := K) I.2)
def unflat (K ℓ v : ℕ) (w : List Bool) : List (List Bool) :=
  (List.range K).map fun u => if u = v then [] else block ℓ (if u < v then u else u - 1) w
def tabulate (pad : U) (K ℓ : ℕ) (F : IQ → ℤ) : Tab :=
  (List.range K).map fun v => (rng pad (2 ^ ((K - 1) * ℓ))).map fun i => F (v, unflat K ℓ v (toWord ((K - 1) * ℓ) i))
structure WF (K Λ B : ℕ) (I : PInst) : Prop where
  lam_pos : 1 ≤ I.1.length
  lam_le : I.1.length ≤ Λ
  rows : I.2.length = K
  row_len : ∀ r ∈ I.2, r.length = 2 ^ ((K - 1) * I.1.length)
  abs_le : ∀ r ∈ I.2, ∀ z ∈ r, z.natAbs ≤ 2 ^ B
def freeM {α β : Type} (f : α → β) : Stepped α β where
  σ := α
  sz := ⟨fun _ => 0⟩
  init := id
  step := id
  out a := some (f a)
structure FNet (C : Type) where
  n : C → ℕ → ℕ
  cap : C → ℕ → ℕ → ℕ
  W : C × WQ → ℤ
  f : C × FQ → ℤ
def FNet.toP {C : Type} (F : FNet C) : PNet C := ⟨F.n, F.cap, freeM F.W, freeM F.f⟩
end PaddedDescent.F


