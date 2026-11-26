-- Prove2me | Definitions.Def_EconomicsNextProof_Mobius
-- name    : EconomicsNextProof_Mobius
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:12:43.742232+00:00
-- url     : https://prove2.me/theorems/a5b44ba4-1bca-40c5-aba8-3900aeacc0e0
-- title:
--   Mobius
-- statement:
--   Definitions and structural lemmas for Mobius, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/falmagne-block-marschak-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Falmagne-Block-Marschak random-utility characterization of stochastic choice rules development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Mobius.lean

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace EconomicsNextProof
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]
noncomputable def upperSum (f : Finset X → ℝ) (A : Finset X) : ℝ :=
  ∑ B ∈ Finset.univ.filter (fun B : Finset X => A ⊆ B), f B
noncomputable def upperMobius (f : Finset X → ℝ) (A : Finset X) : ℝ :=
  ∑ B ∈ Finset.univ.filter (fun B : Finset X => A ⊆ B),
    (-1 : ℝ) ^ (B \ A).card * f B
noncomputable def booleanMu : IncidenceAlgebra ℝ (Finset X) where
  toFun A B := if A ⊆ B then (-1 : ℝ) ^ (B \ A).card else 0
  eq_zero_of_not_le' := by intros; simp_all
noncomputable def upperSumLinear :
    (Finset X → ℝ) →ₗ[ℝ] (Finset X → ℝ) where
  toFun := upperSum
  map_add' f g := by
    funext A
    simp [upperSum, Finset.sum_add_distrib]
  map_smul' r f := by
    funext A
    simp [upperSum, Finset.mul_sum]
end EconomicsNextProof


