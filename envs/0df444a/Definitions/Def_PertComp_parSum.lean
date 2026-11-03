-- Prove2me | Definitions.Def_PertComp_parSum
-- name    : PertComp_parSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:19.178839+00:00
-- url     : https://prove2.me/theorems/5b511225-c8c3-44c6-a90e-7bac1edb44a6
-- title:
--   Parallel sum $A\,\Box\,B$ of set-valued operators
-- statement:
--   For set-valued operators $A,B\colon X\to 2^{X^*}$, the **parallel sum** is $A\,\Box\,B=(A^{-1}+B^{-1})^{-1}$. Unfolded: $y^*\in(A\,\Box\,B)(y)$ if and only if $y=y_1+y_2$ for some $y_1,y_2$ with $y^*\in Ay_1$ and $y^*\in By_2$.
--
--   It is used in Lemma 2.7, $(\partial f)\,\Box\,(\partial g)=\partial(f\,\Box\,g)$, and in the operator $\boldsymbol B$ of (3.6).
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, (2.3), p.5

import Mathlib

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, (2.3), p.5: the *parallel sum*
`A □ B = (A⁻¹ + B⁻¹)⁻¹` of set-valued operators `A, B : X → 2^{X*}`.

**Formalization Note.** Unfolded: `y* ∈ (A □ B)(y)` iff `y ∈ A⁻¹(y*) + B⁻¹(y*)`, i.e. iff
`y = y₁ + y₂` with `y* ∈ A(y₁)` and `y* ∈ B(y₂)`. -/
def parSum {V W : Type*} [Add V] (A B : V → Set W) (y : V) : Set W :=
  {y' | ∃ y₁ y₂ : V, y = y₁ + y₂ ∧ y' ∈ A y₁ ∧ y' ∈ B y₂}

end PertComp


