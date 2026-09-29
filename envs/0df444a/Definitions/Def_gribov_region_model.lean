-- Prove2me | Definitions.Def_gribov_region_model
-- name    : gribov_region_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T17:55:31.732536+00:00
-- url     : https://prove2.me/theorems/31699884-acd3-4f9d-a8ae-413bb00d5732
-- title:
--   Faddeev--Popov operator model and the Gribov region $\Omega$
-- statement:
--   A finite-dimensional model of the Landau-gauge Faddeev--Popov operator and of the Gribov region it defines.
--
--   Configurations form a real vector space $V$; the Faddeev--Popov operator acts on an $n$-dimensional space and is represented by a real $n \times n$ matrix. A model consists of a field-independent part $M_0$, assumed symmetric positive definite (the operator $-\partial^2$ of the review), together with a linear map $A \mapsto M_2(A)$ whose values are symmetric traceless matrices (the part $\partial_\mu f^{abc}A_\mu^c$ of Eq. (2.53), traceless in the colour indices). The Faddeev--Popov operator of a configuration is
--
--   $$ M(A) = M_0 + M_2(A), $$
--
--   and the **Gribov region** is the set
--
--   $$ \Omega = \{ A \in V : M(A) \text{ is positive definite} \}, $$
--
--   which is Eq. (2.52) of the review with positivity in the sense of Eq. (2.54).
-- source:
--   N. Vandersickel, D. Zwanziger, The Gribov problem and QCD dynamics, Physics Reports 520 (2012) 175-251, doi:10.1016/j.physrep.2012.07.003, Section 2.2.1 (pp. 188-189), Eqs. (2.52)-(2.59)

import Mathlib

set_option autoImplicit false

namespace GribovRegion

open scoped Matrix

/-- A finite-dimensional model of the Landau-gauge Faddeev–Popov operator.

`V` is the (real) vector space of transverse gauge-field configurations
`A` and `Fin n` indexes the finite-dimensional space on which the
Faddeev–Popov operator acts (colour times the truncated space of
fluctuations `ω`).

* `base` is the field-independent part `M₀ = -∂²` of the Faddeev–Popov
  operator, assumed symmetric positive definite (on the non-constant modes);
* `lin` is the field-dependent part `A ↦ M₂(A)`, which is linear in `A`,
  symmetric, and traceless.

The Faddeev–Popov operator of the configuration `A` is then
`M(A) = M₀ + M₂(A)`. -/
structure FPModel (V : Type*) [AddCommGroup V] [Module ℝ V] (n : ℕ) where
  /-- The field-independent part `M₀` of the Faddeev–Popov operator. -/
  base : Matrix (Fin n) (Fin n) ℝ
  /-- The field-dependent part `A ↦ M₂(A)`, linear in `A`. -/
  lin : V →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ
  /-- `M₀` is symmetric positive definite. -/
  base_posDef : base.PosDef
  /-- Each `M₂(A)` is symmetric. -/
  lin_isHermitian : ∀ A : V, (lin A).IsHermitian
  /-- Each `M₂(A)` is traceless. -/
  lin_trace_zero : ∀ A : V, (lin A).trace = 0

/-- The Faddeev–Popov operator `M(A) = M₀ + M₂(A)` of the configuration `A`. -/
def fpOperator {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (m : FPModel V n) (A : V) : Matrix (Fin n) (Fin n) ℝ :=
  m.base + m.lin A

/-- The Gribov region `Ω`: the set of configurations whose Faddeev–Popov
operator `M(A) = M₀ + M₂(A)` is positive definite. -/
def region {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (m : FPModel V n) : Set V :=
  {A : V | (fpOperator m A).PosDef}

@[simp]
theorem fpOperator_apply {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (m : FPModel V n) (A : V) : fpOperator m A = m.base + m.lin A := rfl

@[simp]
theorem mem_region_iff {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (m : FPModel V n) (A : V) :
    A ∈ region m ↔ (fpOperator m A).PosDef := Iff.rfl

end GribovRegion


