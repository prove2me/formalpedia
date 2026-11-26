-- Prove2me | Definitions.Def_N4Code_Definitions
-- name    : N4Code_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:53:11.420996+00:00
-- url     : https://prove2.me/theorems/a8a3fd42-c5a1-569c-897d-faaadb8ca442
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from Shenghao Yang, Yanyan Dong (shhyang/n4code_lean; see pinned Apache-2.0 LICENSE)'s pinned N4Code: optimal finite-length block codes of size four for binary symmetric channels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean

import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option autoImplicit true
open scoped BigOperators
noncomputable section
namespace N4Code
set_option maxRecDepth 1000000
abbrev Word (n : ℕ) := Fin n → Bool
def bitXor {n : ℕ} (x y : Word n) : Word n := fun i => Bool.xor (x i) (y i)
def hammingWeight {n : ℕ} (x : Word n) : ℕ :=
  ∑ i ∈ (Finset.univ : Finset (Fin n)), if x i = true then 1 else 0
def hammingDist {n : ℕ} (x y : Word n) : ℕ := hammingWeight (bitXor x y)
abbrev Column := Fin 4 → Bool
def colBit (j : Fin 4) (c : Column) : Bool := c j
def colVal (c : Column) : ℕ := ∑ j : Fin 4, if c j then 2 ^ (3 - j.val) else 0
def flipCol (c : Column) : Column := fun j => !(c j)
def rowPermute (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) : Column := fun j => c (ρ j)
abbrev Code (n : ℕ) := Fin n → Column
def row {n : ℕ} (C : Code n) (j : Fin 4) : Word n := fun t => colBit j (C t)
def row0 {n : ℕ} (C : Code n) : Word n := row C ⟨0, by decide⟩
def row1 {n : ℕ} (C : Code n) : Word n := row C ⟨1, by decide⟩
def row2 {n : ℕ} (C : Code n) : Word n := row C ⟨2, by decide⟩
def row3 {n : ℕ} (C : Code n) : Word n := row C ⟨3, by decide⟩
def DistinctRows {n : ℕ} (C : Code n) : Prop :=
  ∀ i j : Fin 4, i ≠ j → row C i ≠ row C j
def count {n : ℕ} (C : Code n) (i : ℕ) : ℕ :=
  ∑ t : Fin n, if colVal (C t) = i then 1 else 0
def totalCounts {n : ℕ} (C : Code n) (types : Finset ℕ) : ℕ :=
  ∑ i ∈ types, count C i
def weightOn {n : ℕ} (y : Word n) (s : Finset (Fin n)) : ℕ :=
  (s.filter fun t => y t = true).card
def w_i {n : ℕ} (C : Code n) (i : ℕ) (y : Word n) : ℕ :=
  weightOn y (Finset.univ.filter fun t => colVal (C t) = i)
def dRow {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) : ℕ := hammingDist (row C j) y
def dCode {n : ℕ} (C : Code n) (y : Word n) : ℕ :=
  min (hammingDist (row0 C) y)
    (min (hammingDist (row1 C) y) (min (hammingDist (row2 C) y) (hammingDist (row3 C) y)))
def alpha {n : ℕ} (C : Code n) (d : ℕ) : ℕ :=
  ∑ y : Word n, if dCode C y = d then 1 else 0
def lambda {n : ℕ} (C : Code n) (ε : ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ y : Word n, (1 - ε) ^ (n - dCode C y) * ε ^ (dCode C y)
def UniversalBetter {n : ℕ} (C₁ C₂ : Code n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → lambda C₁ ε ≥ lambda C₂ ε
def UniversalStrictBetter {n : ℕ} (C₁ C₂ : Code n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → lambda C₁ ε > lambda C₂ ε
def UniversalEqual {n : ℕ} (C₁ C₂ : Code n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → lambda C₁ ε = lambda C₂ ε
def OptimalAt {n : ℕ} (C : Code n) (ε : ℝ) : Prop :=
  ∀ D : Code n, lambda C ε ≥ lambda D ε
def Equivalent {n : ℕ} (C C' : Code n) : Prop :=
  ∃ ρ : Equiv (Fin 4) (Fin 4), ∃ p : Equiv (Fin n) (Fin n), ∃ f : Fin n → Bool,
    ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t)
def col0 : Column := fun _ => false
def col1 : Column := fun j => j.val = 3
def col3 : Column := fun j => j.val = 2 ∨ j.val = 3
def col5 : Column := fun j => j.val = 1 ∨ j.val = 3
def col6 : Column := fun j => j.val = 1 ∨ j.val = 2
def col7 : Column := fun j => j.val = 1 ∨ j.val = 2 ∨ j.val = 3
example : colVal col0 = 0 := by decide
example : colVal col1 = 1 := by decide
example : colVal col3 = 3 := by decide
example : colVal col5 = 5 := by decide
example : colVal col6 = 6 := by decide
example : colVal col7 = 7 := by decide
def Columns07 {n : ℕ} (C : Code n) : Prop := ∀ t : Fin n, C t 0 = false
def IsLinear {n : ℕ} (C : Code n) : Prop :=
  (∀ t : Fin n, colVal (C t) = 0 ∨ colVal (C t) = 3 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6) ∧
    ((count C 3 > 0 ∧ count C 5 > 0) ∨ (count C 3 > 0 ∧ count C 6 > 0) ∨
      (count C 5 > 0 ∧ count C 6 > 0))
def ClassI {n : ℕ} (C : Code n) : Prop :=
  Odd (count C 1) ∧
    ((Even (count C 3) ∧ Even (count C 5) ∧ Even (count C 6)) ∨
      (Odd (count C 3) ∧ Odd (count C 5) ∧ Odd (count C 6))) ∧
    totalCounts C {1, 3, 5, 6} = n
def ClassII {n : ℕ} (C : Code n) : Prop :=
  count C 1 > 0 ∧ totalCounts C {1, 3, 5, 6} = n ∧
    ((Even (count C 1) ∧ Even (count C 3) ∧ Odd (count C 5) ∧ Odd (count C 6)) ∨
      (Even (count C 1) ∧ Odd (count C 3) ∧ Even (count C 5) ∧ Even (count C 6)))
def ClassIII {n : ℕ} (C : Code n) : Prop :=
  totalCounts C {1, 3, 5, 6, 7} = n ∧
    ((count C 1 = 1 ∧ count C 7 = 1 ∧ count C 6 = 0 ∧ Even (count C 3) ∧
        Odd (count C 5)) ∨
      (count C 1 = 1 ∧ count C 5 = 0 ∧ count C 7 = 0 ∧ Odd (count C 3) ∧
        Odd (count C 6)))
def SameParity (a b c : ℕ) : Prop :=
  (Even a ↔ Even b) ∧ (Even b ↔ Even c)
def linearCode (n3 n5 n6 : ℕ) : Code (n3 + n5 + n6) :=
  fun t =>
    if t.val < n3 then col3
    else if t.val < n3 + n5 then col5
    else col6
def flipBit {n : ℕ} (t : Fin n) (y : Word n) : Word n :=
  fun u => if u = t then !(y u) else y u
def flipTwoBits {n : ℕ} (t₁ t₂ : Fin n) (y : Word n) : Word n :=
  fun u => if u = t₁ ∨ u = t₂ then !(y u) else y u
def replaceColumn {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) : Code n :=
  fun u => if u = t then s' else C u
def dO {n : ℕ} (C : Code n) (y : Word n) : ℕ :=
  min (hammingDist (row0 C) y) (min (hammingDist (row1 C) y) (hammingDist (row3 C) y))
def dP {n : ℕ} (C : Code n) (y : Word n) : ℕ := hammingDist (row2 C) y
def dOp {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : ℕ := dO C (flipBit t y)
def dPp {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : ℕ := dP C (flipBit t y)
def dOp2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : ℕ := dO C (flipTwoBits t₁ t₂ y)
def dPp2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : ℕ := dP C (flipTwoBits t₁ t₂ y)
def Y1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  (dO C y ≤ dP C y ∧ dP C y < dPp C t y) ∨
    (dO C y ≤ dPp C t y ∧ dPp C t y ≤ dP C y ∧ dOp C t y ≤ dPp C t y)
def Y2 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  (dP C y ≤ dPp C t y ∧ dP C y < dO C y) ∨
    (dPp C t y < dP C y ∧ dP C y ≤ dO C y ∧ dP C y ≤ dOp C t y)
def Y3 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  dPp C t y = dOp C t y ∧ dPp C t y < dP C y ∧ dP C y = dO C y
def Y4 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  dP C y = dPp C t y ∧ dPp C t y = dO C y ∧ dO C y < dOp C t y
def Y5 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Prop :=
  dPp C t y = dO C y ∧ dOp C t y = dP C y ∧ dO C y < dOp C t y
instance decY1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Decidable (Y1 C t y) := by
  unfold Y1; infer_instance
instance decY2 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Decidable (Y2 C t y) := by
  unfold Y2; infer_instance
instance decY3 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Decidable (Y3 C t y) := by
  unfold Y3; infer_instance
instance decY4 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Decidable (Y4 C t y) := by
  unfold Y4; infer_instance
instance decY5 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Decidable (Y5 C t y) := by
  unfold Y5; infer_instance
def YSet {n : ℕ} (C : Code n) (t : Fin n) (i : Fin 5) (y : Word n) : Prop :=
  if i.val = 0 then Y1 C t y
  else if i.val = 1 then Y2 C t y
  else if i.val = 2 then Y3 C t y
  else if i.val = 3 then Y4 C t y
  else Y5 C t y
def g1 {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) : Word n :=
  if Y1 C t y ∨ Y3 C t y then y else flipBit t y
def alpha3 {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) : ℕ :=
  (Finset.univ.filter fun y : Word n => Y3 C t y ∧ dCode C y = d).card
def alpha5 {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) : ℕ :=
  (Finset.univ.filter fun y : Word n => Y5 C t y ∧ dCode C y = d).card
def Psi {n : ℕ} (C : Code n) (t : Fin n) (d : ℕ) : ℤ :=
  (∑ i ∈ Finset.Icc 1 d, (alpha3 C t i : ℤ)) -
    ∑ i ∈ Finset.Icc 0 (d - 1), (alpha5 C t i : ℤ)
def Z1 {n : ℕ} (_C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Prop := y t₁ = y t₂
def Z2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Prop :=
  y t₁ ≠ y t₂ ∧ dO C y ≤ min (dP C y) (dPp2 C t₁ t₂ y)
def Z3 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Prop :=
  y t₁ ≠ y t₂ ∧ dO C y > min (dP C y) (dPp2 C t₁ t₂ y) ∧
    dP C y ≤ min (dO C y) (dOp2 C t₁ t₂ y)
def Z4 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Prop :=
  y t₁ ≠ y t₂ ∧ dO C y > min (dP C y) (dPp2 C t₁ t₂ y) ∧
    dP C y > min (dO C y) (dOp2 C t₁ t₂ y) ∧
    dPp2 C t₁ t₂ y < min (dO C y) (dOp2 C t₁ t₂ y)
def Z5 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Prop :=
  y t₁ ≠ y t₂ ∧ dO C y > min (dP C y) (dPp2 C t₁ t₂ y) ∧
    dP C y > min (dO C y) (dOp2 C t₁ t₂ y) ∧
    min (dO C y) (dOp2 C t₁ t₂ y) ≤ dPp2 C t₁ t₂ y
def Z41 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Prop :=
  Z4 C t₁ t₂ y ∧ min (dO C y) (dP C y) > dOp2 C t₁ t₂ y
instance decZ1 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    Decidable (Z1 C t₁ t₂ y) := by
  unfold Z1; infer_instance
instance decZ2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    Decidable (Z2 C t₁ t₂ y) := by
  unfold Z2; infer_instance
instance decZ3 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    Decidable (Z3 C t₁ t₂ y) := by
  unfold Z3; infer_instance
instance decZ4 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    Decidable (Z4 C t₁ t₂ y) := by
  unfold Z4; infer_instance
instance decZ5 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    Decidable (Z5 C t₁ t₂ y) := by
  unfold Z5; infer_instance
instance decZ41 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    Decidable (Z41 C t₁ t₂ y) := by
  unfold Z41; infer_instance
def ZSet {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (i : Fin 5) (y : Word n) : Prop :=
  if i.val = 0 then Z1 C t₁ t₂ y
  else if i.val = 1 then Z2 C t₁ t₂ y
  else if i.val = 2 then Z3 C t₁ t₂ y
  else if i.val = 3 then Z4 C t₁ t₂ y
  else Z5 C t₁ t₂ y
def g2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) : Word n :=
  if Z1 C t₁ t₂ y ∨ Z2 C t₁ t₂ y ∨ Z5 C t₁ t₂ y then y
  else flipTwoBits t₁ t₂ y
def argminType {n : ℕ} (C : Code n) : Column :=
  if count C 3 ≤ count C 5 ∧ count C 3 ≤ count C 6 then col3
  else if count C 5 ≤ count C 6 then col5
  else col6
def CA : Code 3 := fun t =>
  if t.val = 0 then col3 else if t.val = 1 then col5 else col0
def code135 : Code 3 := fun t =>
  if t.val = 0 then col1 else if t.val = 1 then col5 else col7
def code136 : Code 3 := fun t =>
  if t.val = 0 then col1 else if t.val = 1 then col3 else col6
def InOptimal3 (C : Code 3) : Prop :=
  C = code135 ∨ C = code136 ∨ C = CA ∨ C = linearCode 1 1 1 ∨ C = linearCode 1 2 0
def colOfNat (i : ℕ) : Column := fun j => i.testBit (3 - j.val)
def example74 : Code 7 := fun t => colOfNat (t.val + 1)
example : count example74 1 = 1 := by decide
example : count example74 2 = 1 := by decide
example : count example74 3 = 1 := by decide
example : count example74 4 = 1 := by decide
example : count example74 5 = 1 := by decide
example : count example74 6 = 1 := by decide
example : count example74 7 = 1 := by decide
example : (∑ i ∈ Finset.Icc 1 7, count example74 i) = 7 := by decide
end N4Code


