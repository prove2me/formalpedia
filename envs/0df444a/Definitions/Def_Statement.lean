-- Prove2me | Definitions.Def_Statement
-- name    : Statement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:34:01.098592+00:00
-- url     : https://prove2.me/theorems/4d6e9117-7f76-4416-bf9f-580ecbd5a862
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Colin Snyder / Star Fleet Math; AItoBit (AItoBit/erdos-662-proof; see pinned Apache-2.0 LICENSE and NOTICE)'s pinned Erdos 662: corrected global threshold conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Statement.lean

module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Prod
public import Mathlib.SetTheory.Cardinal.Finite
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Erdos662
noncomputable def euclideanDistance (x y : ℝ × ℝ) : ℝ :=
  Real.sqrt ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)
noncomputable def triangularNeighborCount (t : ℝ) : ℕ :=
  Nat.card {d : ℤ × ℤ // d ≠ (0, 0) ∧
    (d.1 : ℝ) ^ 2 + (d.1 : ℝ) * (d.2 : ℝ) + (d.2 : ℝ) ^ 2 ≤ t ^ 2}
def OneSeparated {α : Type*} (p : α → ℝ × ℝ) : Prop :=
  ∀ i j, i ≠ j → 1 ≤ euclideanDistance (p i) (p j)
noncomputable def closeDirectedPairs {α : Type*} [Fintype α] [DecidableEq α]
    (t : ℝ) (p : α → ℝ × ℝ) : Finset (α × α) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun q =>
    q.1 ≠ q.2 ∧ euclideanDistance (p q.1) (p q.2) ≤ t
def GlobalThresholdConjecture : Prop :=
  ∀ t : ℝ, 1 ≤ t → ∃ N : ℕ, ∀ (α : Type) [Fintype α] [DecidableEq α],
    N ≤ Fintype.card α → ∀ p : α → ℝ × ℝ,
      OneSeparated p →
        (closeDirectedPairs t p).card ≤ triangularNeighborCount t * Fintype.card α
end Erdos662


