-- Prove2me | Definitions.Def_StepMachines_Math_CutWord
-- name    : StepMachines_Math_CutWord
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:35:56.605126+00:00
-- url     : https://prove2.me/theorems/0759c566-38a0-4d89-a25c-dd47be773d43
-- title:
--   Cut Word
-- statement:
--   Definitions and structural lemmas for Cut Word, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CutWord.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit


set_option autoImplicit false
section
section
namespace Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
def bitsOf (n : ℕ) (w : List Bool) : Bits n := fun k => w.getD k false
theorem bitsOf_bijOn (n : ℕ) : Set.BijOn (bitsOf n) (words n) (univ : Finset (Bits n)) := by
  refine ⟨fun _ _ => mem_coe.2 (mem_univ _), fun w hw w' hw' h => ?_, fun x _ => ?_⟩
  · have l := mem_words.1 (mem_coe.1 hw)
    have l' := mem_words.1 (mem_coe.1 hw')
    refine List.ext_getElem (l.trans l'.symm) fun j hj hj' => ?_
    have h1 := congrFun h ⟨j, l ▸ hj⟩
    simpa only [bitsOf, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] using h1
  · refine ⟨List.ofFn x, mem_coe.2 (mem_words.2 (List.length_ofFn)), funext fun k => ?_⟩
    rw [bitsOf, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact k.2), List.getElem_ofFn]
def bitsC (n : ℕ) : Code (univ : Finset (Bits n)) n := (Code.word n).map (bitsOf n) univ (bitsOf_bijOn n)
def sideBit (tr : Bool) : BitCut := if tr = true then colBit else rowBit
def sideS0 (tr : Bool) : Bell := if tr = true then (false, false) else (true, true)
def sideCnt (tr : Bool) (n i : ℕ) : ℕ := if tr = true then i else n - i
def sideCut (tr : Bool) (n i : ℕ) : Cut (Bits n) (Fin n → Bell) where
  lab := sparseLab (sideS0 tr) n (sideCnt tr n i)
  top x y β := (sideBit tr).Top β x y
  bot u v β := (sideBit tr).Bot i β u v
  cap := capW n (sideCnt tr n i)
def topTerm (tr : Bool) (x y w : List Bool) (k : ℕ) : ℤ :=
  (sideBit tr).top (symAt (sideS0 tr) x.length w k) (x.getD k false) (y.getD k false)
def botTerm (tr : Bool) (x y w : List Bool) (s k : ℕ) : ℤ :=
  if (toWord x.length s).getD k false = true then
    (sideBit tr).bot1 (symAt (sideS0 tr) x.length w k) (x.getD k false) (y.getD k false)
  else (sideBit tr).bot0 (symAt (sideS0 tr) x.length w k) (x.getD k false) (y.getD k false)
def topW (tr : Bool) (x y w : List Bool) : ℤ := ∏ k ∈ range x.length, topTerm tr x y w k
def botW (tr : Bool) (i : ℕ) (x y w : List Bool) : ℤ :=
  ∑ s ∈ range (2 ^ x.length),
    if (toWord x.length s).count true = i then ∏ k ∈ range x.length, botTerm tr x y w s k else 0
def cutW (tr top : Bool) (i : ℕ) (x y w : List Bool) : ℤ :=
  if validW x.length (sideCnt tr x.length i) w = true then
    if top = true then topW tr x y w else botW tr i x y w
  else 0
end Groundwork.Grid


