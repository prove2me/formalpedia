-- Prove2me | Definitions.Def_PaddedDescent_F_MarkMath
-- name    : PaddedDescent_F_MarkMath
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:35:14.324491+00:00
-- url     : https://prove2.me/theorems/0ecee8f5-dea4-4bba-99d9-fcabfc22c090
-- title:
--   Mark Math
-- statement:
--   Definitions and structural lemmas for Mark Math, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkMath.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
set_option autoImplicit false
section
section
namespace PaddedDescent.F.Mark
open Groundwork Groundwork.Prog
abbrev Cl := List (ℕ × Bool)
def vio (σ : ℕ → Bool) (C : Cl) : Bool := C.all fun l => σ l.1 != l.2
def nvio (σ : ℕ → Bool) (L : Fml) : ℕ := L.countP (vio σ)
def Tpl (w v : ℕ) : ℤ := ∑ j ∈ Finset.range (w + 1), (v.choose j : ℤ)
def Tsg (w v : ℕ) : ℤ := ∑ j ∈ Finset.range (w + 1), (-1) ^ j * (v.choose j : ℤ)
def ext {n : ℕ} (σ : Fin n → Bool) (x : ℕ) : Bool := if h : x < n then σ ⟨x, h⟩ else false
def trunc (n w : ℕ) (Ls : List Fml) : ℤ :=
  ∑ σ : Fin n → Bool, Tpl w (nvio (ext σ) (Ls.headD [])) * (Ls.tail.map fun L => Tsg w (nvio (ext σ) L)).prod
def Good (n w : ℕ) : List Fml → Prop
  | [] => True
  | Λ :: rest => (∀ σ : Fin n → Bool, (∀ L ∈ rest, nvio (ext σ) L = 0) → nvio (ext σ) Λ ≤ w) ∧ Good n w rest
def nSat (n : ℕ) (ψ : Fml) : ℕ := (Finset.univ.filter fun σ : Fin n → Bool => ∀ C ∈ ψ, ∃ l ∈ C, ext σ l.1 = l.2).card
def occ (x : Fml) (v : ℕ) : Fml := x.filter fun C => C.any fun l => l.1 == v
def dropE (ev : List Fml → ℤ) (w : ℕ) (Ls : List Fml) (C : Cl) (i : ℕ) : Bool :=
  decide ((ev ((C :: Ls.getD i []) :: Ls.drop (i + 1)) - ev (Ls.drop i)) * ((2 ^ ((Ls.drop i).flatten.length + 3) : ℕ) : ℤ) ≤
    ((3 ^ (Ls.drop (i + 1)).flatten.length * 2 ^ w : ℕ) : ℤ))
def placeAt (Ls : List Fml) (C : Cl) (i : ℕ) : List Fml := Ls.take i ++ (C :: Ls.getD i []) :: Ls.drop (i + 1)
def placeE (ev : List Fml → ℤ) (w : ℕ) (Ls : List Fml) (C : Cl) : List Fml :=
  placeAt Ls C (((List.range (Ls.length - 1)).find? (dropE ev w Ls C)).getD (Ls.length - 1))
def layersE (ev : List Fml → ℤ) (w R : ℕ) (ψ : Fml) : List Fml := ψ.foldl (placeE ev w) (List.replicate (R + 1) [])
def Asked (n w R : ℕ) (ψ : Fml) (Ls : List Fml) : Prop := Good n w Ls ∧ Ls.length ≤ R + 2 ∧ Ls.flatten.Subperm ψ
end PaddedDescent.F.Mark


