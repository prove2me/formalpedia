-- Prove2me | Definitions.Def_CoprimeAdjacencies_Statement
-- name    : CoprimeAdjacencies_Statement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T19:00:01.334738+00:00
-- url     : https://prove2.me/theorems/301af511-e7dd-4f63-b2ce-88b85b38f76b
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from G. Sidoine and contributors's pinned Minimum coprime adjacencies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Statement.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace P010
def IsPermutation (n : ℕ) (a : List ℕ) : Prop :=
  a.Perm (List.range' 1 n)
def adjacentCount (a : List ℕ) : ℕ :=
  (a.zip a.tail).countP (fun z => decide (Nat.Coprime z.1 z.2))
def pi (n : ℕ) : ℕ := Nat.primeCounting n
def target (n : ℕ) : ℕ :=
  (pi n - pi (n / 2)) +
    max 1 (((pi (n / 2) - pi (n / 3)) + 1) / 2)
def Attained (n k : ℕ) : Prop :=
  ∃ a : List ℕ, IsPermutation n a ∧ adjacentCount a = k
theorem attainable (n : ℕ) : ∃ k : ℕ, Attained n k := by
  refine ⟨adjacentCount (List.range' 1 n), List.range' 1 n, ?_, rfl⟩
  exact List.Perm.refl _
noncomputable def h (n : ℕ) : ℕ := by
  classical
  exact Nat.find (attainable n)
def ExactStatement (n : ℕ) : Prop := 4 ≤ n → h n = target n
end P010


