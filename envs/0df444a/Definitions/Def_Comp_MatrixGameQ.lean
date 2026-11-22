-- Prove2me | Definitions.Def_Comp_MatrixGameQ
-- name    : Comp_MatrixGameQ
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:43:21.083557+00:00
-- url     : https://prove2.me/theorems/45bc80dd-81f0-461a-ab60-26b68a77cbbc
-- title:
--   Matrix Game Q
-- statement:
--   Definitions and structural lemmas for Matrix Game Q, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/MatrixGameQ.lean

import Definitions.Def_Comp_Basic
set_option autoImplicit true
namespace Comp
open Csg
section Strategies
variable {I : Type*} [Fintype I]
def IsStratQ (p : I → ℚ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1
instance (p : I → ℚ) : Decidable (IsStratQ p) := by
  unfold IsStratQ
  infer_instance
end Strategies
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
structure MatrixGameQ (I J : Type*) [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J] where
  /-- The rational payoff matrix. -/
  A : I → J → ℚ
namespace MatrixGameQ
noncomputable def toMatrixGame (G : MatrixGameQ I J) : MatrixGame I J where
  A i j := ((G.A i j : ℚ) : ℝ)
def ValueCert (G : MatrixGameQ I J) (t : ℚ) (p : I → ℚ) (q : J → ℚ) : Prop :=
  IsStratQ p ∧ IsStratQ q ∧ (∀ j, ∑ i, p i * G.A i j ≤ t) ∧ (∀ i, t ≤ ∑ j, G.A i j * q j)
instance (G : MatrixGameQ I J) (t : ℚ) (p : I → ℚ) (q : J → ℚ) : Decidable (G.ValueCert t p q) := by
  unfold ValueCert
  infer_instance
end MatrixGameQ
structure BimatrixQ (I J : Type*) [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J] where
  /-- The row player's own payoff, which it maximises. -/
  R : I → J → ℚ
  /-- The column player's own payoff, which it maximises. -/
  C : I → J → ℚ
namespace BimatrixQ
def rowPayoff (G : BimatrixQ I J) (p : I → ℚ) (q : J → ℚ) : ℚ := ∑ i, ∑ j, p i * G.R i j * q j
def colPayoff (G : BimatrixQ I J) (p : I → ℚ) (q : J → ℚ) : ℚ := ∑ i, ∑ j, p i * G.C i j * q j
def NashCert (G : BimatrixQ I J) (p : I → ℚ) (q : J → ℚ) : Prop :=
  IsStratQ p ∧ IsStratQ q
    ∧ (∀ i, (∑ j, G.R i j * q j) ≤ G.rowPayoff p q)
    ∧ (∀ j, (∑ i, p i * G.C i j) ≤ G.colPayoff p q)
    ∧ (∀ i, p i = 0 ∨ (∑ j, G.R i j * q j) = G.rowPayoff p q)
    ∧ (∀ j, q j = 0 ∨ (∑ i, p i * G.C i j) = G.colPayoff p q)
instance (G : BimatrixQ I J) (p : I → ℚ) (q : J → ℚ) : Decidable (G.NashCert p q) := by
  unfold NashCert
  infer_instance
end BimatrixQ
namespace MatrixGameQ
def toBimatrixQ (G : MatrixGameQ I J) : BimatrixQ I J where
  R i j := -G.A i j
  C i j := G.A i j
end MatrixGameQ
end Comp


