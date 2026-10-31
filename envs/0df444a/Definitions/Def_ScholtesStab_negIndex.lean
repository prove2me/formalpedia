-- Prove2me | Definitions.Def_ScholtesStab_negIndex
-- name    : ScholtesStab_negIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:28.535582+00:00
-- url     : https://prove2.me/theorems/432d1e0e-f9f8-4b36-b380-3649d5fe7f56
-- title:
--   Negative index of a bilinear form on a subspace; nonsingular restriction
-- statement:
--   Let $B$ be a bilinear form on $\mathbb R^n$ (such as a Hessian $D^2L(\bar x)$) and $\mathcal T\subseteq\mathbb R^n$ a linear subspace. The **negative index** of $B$ on $\mathcal T$ is
--
--   $$
--   \operatorname{negIndex}(B,\mathcal T)=\max\{\dim W \mid W\subseteq\mathcal T \text{ a subspace},\ B(\xi,\xi)<0 \text{ for all } \xi\in W\setminus\{0\}\}.
--   $$
--
--   By Sylvester's law of inertia this is the number of negative eigenvalues (with multiplicity) of the matrix of the restriction $B\restriction_{\mathcal T}$ in any basis of $\mathcal T$, which is the quantity the paper calls the quadratic index. The restriction is **nonsingular** if the only $\xi\in\mathcal T$ with $B(\xi,\eta)=0$ for all $\eta\in\mathcal T$ is $\xi=0$, i.e. the matrix of $B\restriction_{\mathcal T}$ has trivial kernel.
--
--   **Formalization Note** `negIndex` is a supremum over natural numbers; the admissible set contains $0$ ($W=\{0\}$) and is bounded by $\dim\mathcal T$, so the supremum is a maximum. Nonsingularity is that of the restriction to $\mathcal T$, not of $B$ on all of $\mathbb R^n$.
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, p.6, Definition 3 (NDC3) and Definition 4; p.8, Definition 7 (ND3) and Definition 8

import Mathlib

namespace ScholtesStab

/-- **Number of negative eigenvalues of a restricted Hessian** `B↾T`
(Lämmel–Shikhman, arXiv:2501.07383v2, Definition 4, p.6, and Definition 8, p.8: "The number of
negative eigenvalues of the matrix D²L(x̄)↾𝒯_x̄").

For a bilinear form `B` on `V` and a linear subspace `T`, `negIndex B T` is the largest
dimension of a subspace `W ⊆ T` on which `B` is negative definite (`B ξ ξ < 0` for every
nonzero `ξ ∈ W`).

**Formalization Note.** For a symmetric `B` (such as the Hessian of a `C²` function) and a
basis `v₁, …, v_d` of `T`, the matrix of `B↾T` is `(B vₖ vₗ)ₖₗ`; by Sylvester's law of inertia,
its number of negative eigenvalues (with multiplicity) equals this largest dimension, whichever
basis is used. The set of admissible `k` contains `0` (take `W = ⊥`) and, for finite-dimensional
`T`, is bounded by `dim T`, so the supremum is attained. -/
noncomputable def negIndex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (T : Submodule ℝ V) : ℕ :=
  sSup {k | ∃ W : Submodule ℝ V, W ≤ T ∧ Module.finrank ℝ W = k ∧
    ∀ ξ ∈ W, ξ ≠ 0 → B ξ ξ < 0}

/-- **The restricted matrix `B↾T` is nonsingular** (NDC3, p.6; ND3, p.8): the only `ξ ∈ T`
with `B ξ η = 0` for all `η ∈ T` is `ξ = 0`.

**Formalization Note.** In a basis of `T` this says that the square matrix `(B vₖ vₗ)ₖₗ` has
trivial kernel, i.e. is nonsingular. It is not the nonsingularity of `B` on the whole space. -/
def NonsingularOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (T : Submodule ℝ V) : Prop :=
  ∀ ξ ∈ T, (∀ η ∈ T, B ξ η = 0) → ξ = 0

end ScholtesStab


