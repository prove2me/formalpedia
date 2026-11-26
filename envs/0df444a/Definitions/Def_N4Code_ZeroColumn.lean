-- Prove2me | Definitions.Def_N4Code_ZeroColumn
-- name    : N4Code_ZeroColumn
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:09:34.389527+00:00
-- url     : https://prove2.me/theorems/ec41694d-35b2-50e3-a83e-48c2a1708648
-- title:
--   Zero Column
-- statement:
--   Definitions and structural lemmas for Zero Column, from Shenghao Yang, Yanyan Dong (shhyang/n4code_lean; see pinned Apache-2.0 LICENSE)'s pinned N4Code: optimal finite-length block codes of size four for binary symmetric channels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
set_option autoImplicit true
open scoped BigOperators
noncomputable section
namespace N4Code
set_option maxRecDepth 1000000
def dRowMin {n : ℕ} (C : Code n) (S : Finset (Fin 4)) (hS : S.Nonempty) (y : Word n) : ℕ :=
  (S.image fun i => dRow C i y).min' (hS.image fun i => dRow C i y)
def colOnes (s' : Column) : Finset (Fin 4) := Finset.univ.filter fun i => s' i
def colZeros (s' : Column) : Finset (Fin 4) := Finset.univ.filter fun i => ¬ s' i
def dOc {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty) (y : Word n) : ℕ :=
  dRowMin C (colZeros s') hO y
def dPc {n : ℕ} (C : Code n) (s' : Column) (hP : (colOnes s').Nonempty) (y : Word n) : ℕ :=
  dRowMin C (colOnes s') hP y
def g0 {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (t : Fin n) (y : Word n) : Word n :=
  if dOc C s' hO y ≤ dPc C s' hP y then y else flipBit t y
def Y3c {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (t : Fin n) (y : Word n) : Prop :=
  y t = true ∧ dOc C s' hO y = dPc C s' hP y
instance decY3c {n : ℕ} (C : Code n) (s' : Column) (hO : (colZeros s').Nonempty)
    (hP : (colOnes s').Nonempty) (t : Fin n) (y : Word n) : Decidable (Y3c C s' hO hP t y) := by
  unfold Y3c
  infer_instance
def col15 : Column := fun _ => true
lemma colZeros_col5_nonempty : (colZeros col5).Nonempty := by
  rw [colZeros]
  exact ⟨⟨0, by decide⟩, by simp [col5]⟩
lemma colOnes_col5_nonempty : (colOnes col5).Nonempty := by
  rw [colOnes]
  exact ⟨⟨1, by decide⟩, by simp [col5]⟩
def tableK (a4 a5 a6 a7 : ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 1 else if i = 1 ∨ i = 2 ∨ i = 3 then 0
  else if i = 4 then a4 else if i = 5 then a5 else if i = 6 then a6 else if i = 7 then a7 else 0
def C0form {n : ℕ} (C : Code n) : Prop :=
  count C 0 + count C 5 + count C 6 = n ∧ Odd (count C 5) ∧ Odd (count C 6)
def permEven (i j : Fin 4) : Equiv (Fin 4) (Fin 4) :=
  (Equiv.swap i (0 : Fin 4)).trans (Equiv.swap (Equiv.swap i (0 : Fin 4) j) (1 : Fin 4))
def normalizeCode {n : ℕ} (C : Code n) (i j : Fin 4) : Code n :=
  fun t => rowPermute (permEven i j).symm (if (row C i) t then flipCol (C t) else C t)
def swapBits {n : ℕ} (t₁ t' : Fin n) (y : Word n) : Word n :=
  fun u => if u = t₁ then y t' else if u = t' then y t₁ else y u
def twobitCount {n : ℕ} (C : Code n) : ℕ :=
  (Finset.univ.filter fun t : Fin n => colWeight (C t) = 2).card
end N4Code


