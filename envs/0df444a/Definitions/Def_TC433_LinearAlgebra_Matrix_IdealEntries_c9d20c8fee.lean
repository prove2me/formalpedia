-- Prove2me | Definitions.Def_TC433_LinearAlgebra_Matrix_IdealEntries_c9d20c8fee
-- name    : TC433_LinearAlgebra_Matrix_IdealEntries_c9d20c8fee
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:19:02.141072+00:00
-- url     : https://prove2.me/theorems/999448f8-c1cf-4ad6-b37c-70a0c57937a9
-- title:
--   TauCeti: LinearAlgebra / Matrix / IdealEntries
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.Matrix.IdealEntries for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/Matrix/IdealEntries.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.Ideal.BigOperators

/-!
# Matrix entries lying in an ideal

A two-sided ideal containing every entry of a matrix contains every entry of any two-sided
product formed from it, and an ideal contains every entry of any linear combination of matrices
whose entries it contains: each such entry is an `S`-combination of entries of the original
matrices.

Nothing here needs invertibility, a square shape, or a diagonal target — only that the products
are conformable — so the statements are rectangular. Both hold over any `Semiring`; the
two-sided product statement asks the ideal to be two-sided (`Ideal.IsTwoSided`), which is
automatic over a commutative semiring. They are the membership computations a defining-ideal
closure proof performs when it propagates a relation through a matrix identity.

## Main results

* `Matrix.mul_mul_apply_mem`: every entry of `P * A * Q` lies in a two-sided ideal containing
  every entry of `A`.
* `Matrix.sum_smul_apply_mem`: every entry of `∑ a, c a • F a` lies in an ideal containing every
  entry of every `F a`.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace Matrix

variable {l m n o ι S : Type*}

/-- **A two-sided ideal containing the entries of a matrix contains the entries of any two-sided
product formed from it.** Each entry of `P * A * Q` is an `S`-combination of entries of `A`. -/
theorem mul_mul_apply_mem [Semiring S] [Fintype m] [Fintype n] {A : Matrix m n S} {I : Ideal S}
    [I.IsTwoSided] (hA : ∀ i j, A i j ∈ I) (P : Matrix l m S) (Q : Matrix n o S) (i : l) (j : o) :
    (P * A * Q) i j ∈ I := by
  rw [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  exact Ideal.sum_mem _ fun t _ =>
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hA t k))

/-- **An ideal containing the entries of a family of matrices contains the entries of every
linear combination of them.** -/
theorem sum_smul_apply_mem [Semiring S] [Fintype ι] {F : ι → Matrix m n S} {I : Ideal S}
    (hF : ∀ a i j, F a i j ∈ I) (c : ι → S) (i : m) (j : n) :
    (∑ a, c a • F a) i j ∈ I := by
  rw [Matrix.sum_apply]
  refine Ideal.sum_mem _ fun a _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Ideal.mul_mem_left _ _ (hF a i j)

end Matrix


