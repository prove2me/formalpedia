-- Prove2me | Definitions.Def_EconomicsNextProof_Path
-- name    : EconomicsNextProof_Path
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:23:02.340062+00:00
-- url     : https://prove2.me/theorems/e9afdb8e-a791-521b-9dec-b324024848ca
-- title:
--   Path
-- statement:
--   Definitions and structural lemmas for Path, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/falmagne-block-marschak-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Falmagne-Block-Marschak random-utility characterization of stochastic choice rules development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
noncomputable def outflow (q : X → Finset X → ℝ) (A : Finset X) : ℝ :=
  ∑ x ∈ A, q x A
noncomputable def inflow (q : X → Finset X → ℝ) (A : Finset X) : ℝ :=
  ∑ y ∈ Finset.univ \ A, q y (insert y A)
structure IsFlow (q : X → Finset X → ℝ) (m : ℝ) : Prop where
  nonneg : ∀ x A, x ∈ A → 0 ≤ q x A
  source : outflow q Finset.univ = m
  conserve : ∀ A, A.Nonempty → A ≠ Finset.univ → outflow q A = inflow q A
noncomputable def unitEdge (y : X) (B : Finset X) (x : X) (A : Finset X) : ℝ :=
  if x = y ∧ A = B then 1 else 0
noncomputable def pathFlow : List X → X → Finset X → ℝ
  | [], _, _ => 0
  | y :: l, x, A => unitEdge y (y :: l).toFinset x A + pathFlow l x A
end Falmagne


