-- Prove2me | Definitions.Def_GroupTheoreticShannonCapacity_Lattice
-- name    : GroupTheoreticShannonCapacity_Lattice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:25:18.730976+00:00
-- url     : https://prove2.me/theorems/59904e6c-17e0-41c8-8716-1f7ca530dce9
-- title:
--   Lattice
-- statement:
--   Definitions and structural lemmas for Lattice, from jzuiddam/GroupTheoreticShannonCapacity contributors (see pinned LICENSE and source headers)'s pinned Shannon capacity limits from lattice packings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Lattice.lean

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
set_option autoImplicit true
namespace GroupTheoreticShannonCapacity.Lattice
open GroupTheoreticShannonCapacity
open Matrix
def latticeOfMatrix (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  { v | ∃ x : Fin n → ℤ, v = A.mulVec (fun i => (x i : ℝ)) }
noncomputable def inftyNorm (n : ℕ) [NeZero n] (v : Fin n → ℝ) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty) (fun i => |v i|)
noncomputable def minDistance (n : ℕ) [NeZero n] (Λ : Set (Fin n → ℝ)) : ℝ :=
  sInf { d | ∃ v ∈ Λ, v ≠ 0 ∧ d = inftyNorm n v }
def IsPAry (n : ℕ) (p : ℕ) (Λ : Set (Fin n → ℝ)) : Prop :=
  (∀ v : Fin n → ℤ, (fun i => (p * v i : ℝ)) ∈ Λ) ∧
  (∀ v ∈ Λ, ∀ i, ∃ z : ℤ, v i = z)
def latticeQuotient (n : ℕ) (p : ℕ) [NeZero p] (A : Matrix (Fin n) (Fin n) ℤ) :
    Set (Fin n → ZMod p) :=
  { x | ∃ y : Fin n → ℤ, x = fun i => (∑ j, A i j * y j : ZMod p) }
def canonicalRep (p : ℕ) [_hp : NeZero p] (z : ZMod p) : ℤ :=
  if z.val ≤ p / 2 then z.val else (z.val : ℤ) - p
def canonicalRepVec (n : ℕ) (p : ℕ) [hp : NeZero p] (x : Fin n → ZMod p) : Fin n → ℤ :=
  fun i => canonicalRep p (x i)
def intLatticeOfMatrix (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) : AddSubgroup (Fin n → ℤ) where
  carrier := { v | ∃ x : Fin n → ℤ, v = A.mulVec x }
  add_mem' := by
    intro a b ⟨x, hx⟩ ⟨y, hy⟩
    use x + y
    simp only [hx, hy, Matrix.mulVec_add]
  zero_mem' := ⟨0, by simp [Matrix.mulVec_zero]⟩
  neg_mem' := by
    intro a ⟨x, hx⟩
    use -x
    simp only [hx, Matrix.mulVec_neg]
def pZn (n : ℕ) (p : ℕ) : AddSubgroup (Fin n → ℤ) where
  carrier := { v | ∃ x : Fin n → ℤ, v = fun i => p * x i }
  add_mem' := by
    intro a b ⟨x, hx⟩ ⟨y, hy⟩
    use x + y
    ext i
    simp only [hx, hy, Pi.add_apply, mul_add]
  zero_mem' := ⟨0, by ext i; simp⟩
  neg_mem' := by
    intro a ⟨x, hx⟩
    use -x
    ext i
    simp only [hx, Pi.neg_apply, mul_neg]
def modPHom (n : ℕ) (p : ℕ) [NeZero p] : (Fin n → ℤ) →+ (Fin n → ZMod p) where
  toFun v := fun i => (v i : ZMod p)
  map_zero' := by ext i; simp only [Pi.zero_apply, Int.cast_zero]
  map_add' := by intros; ext i; simp only [Pi.add_apply, Int.cast_add]
section Tests
example : (fun i => ((![1, 2] : Fin 2 → ℤ) i : ℝ)) ∈
    latticeOfMatrix 2 (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  use ![1, 2]
  simp only [Matrix.one_mulVec]
example : let A : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; -1, 2]
    (![(2 : ℝ), -1] : Fin 2 → ℝ) ∈ latticeOfMatrix 2 A := by
  refine ⟨![1, 0], ?_⟩
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
example : let A : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; -1, 2]
    (![(1 : ℝ), 2] : Fin 2 → ℝ) ∈ latticeOfMatrix 2 A := by
  refine ⟨![0, 1], ?_⟩
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
example (p : ℕ) : IsPAry 2 p {v : Fin 2 → ℝ | ∀ i, ∃ z : ℤ, v i = z} := by
  constructor
  · intro v i
    exact ⟨p * v i, by simp [Int.cast_mul]⟩
  · intro v hv i
    exact hv i
def exampleA : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; -1, 2]
def exampleB : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; 1, 2]
example : exampleA * exampleB = 5 • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
example : exampleB.det = 5 := by decide
example : exampleA.det = 5 := by decide
end Tests
end GroupTheoreticShannonCapacity.Lattice


