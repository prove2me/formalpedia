-- Prove2me | Definitions.Def_StepMachines_Math_SparsifyProg
-- name    : StepMachines_Math_SparsifyProg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:33:14.507395+00:00
-- url     : https://prove2.me/theorems/468839e7-0b03-47b0-8f39-1523a260b925
-- title:
--   Sparsify Prog
-- statement:
--   Definitions and structural lemmas for Sparsify Prog, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyProg.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyList
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup
set_option autoImplicit false
section
namespace Groundwork.Sparsify
open Finset
public abbrev PLit : Type := ℕ × Bool
public abbrev PCl : Type := List PLit
public abbrev PFml : Type := List PCl
@[expose] public def subP (D C : PCl) : Bool := D.all fun a => C.elem a
@[expose] public def overP (s : PFml) (i : ℕ) (S : PCl) : PFml := s.filter fun C => decide (C.length = i) && subP S C
@[expose] public def addP (A s : PFml) : PFml := A ++ s.filter fun C => !(A.any fun D => subP D C)
@[expose] public def redP (s : PFml) : PFml := s.filter fun C => s.all fun D => !(subP D C) || subP C D
@[expose] public def minusP (H C : PCl) : PCl := C.filter fun a => !(H.elem a)
@[expose] public def litsOf (s : PFml) : PCl := (s.flatMap id).dedup
@[expose] public def canonP (ls C : PCl) : PCl := ls.filter fun a => C.elem a
@[expose] public def rootP (φ : PFml) : PFml := redP ((φ.map fun C => canonP (litsOf φ) C).dedup)
@[expose] public def greedyP : ℕ → PCl → PFml → PFml
  | 0, _, _ => []
  | k + 1, used, l =>
    match l.find? fun Q => Q.all fun a => !(used.elem a) with
    | none => []
    | some Q => Q :: greedyP k (used ++ Q) l
@[expose] public def pickP (τ : ℕ) (s : PFml) : Option (PCl × PFml) :=
  match (litsOf s).find? fun a => decide (τ ≤ (overP s 2 [a]).length) with
  | some a => some ([a], ((overP s 2 [a]).take τ).map (minusP [a]))
  | none =>
    match (List.product (litsOf s) (litsOf s)).find? fun ab =>
        !(ab.1 == ab.2) && decide (τ ≤ (overP s 3 [ab.1, ab.2]).length) with
    | some ab => some ([ab.1, ab.2], ((overP s 3 [ab.1, ab.2]).take τ).map (minusP [ab.1, ab.2]))
    | none =>
      match (litsOf s).find? fun a => decide (2 * τ ^ 3 ≤ (overP s 3 [a]).length) with
      | some a => some ([a], greedyP (τ ^ 2) [] ((overP s 3 [a]).map (minusP [a])))
      | none => none
@[expose] public def stepP (τ : ℕ) (s : PFml) : Option (PFml × PFml) :=
  (pickP τ s).map fun HP => (addP [HP.1] s, addP HP.2 s)
section Eq
end Eq
section Main
abbrev toF (s : PFml) : List (Finset PLit) := s.map List.toFinset
def NodeP (τ : ℕ) (ψ s : PFml) (p q : ℕ) : Prop := (∀ C ∈ s, C.Nodup) ∧ NodeL τ (toF ψ) (toF s) p q
variable {τ n : ℕ} {ψ s l h : PFml} {p q : ℕ}
end Main
end Groundwork.Sparsify


