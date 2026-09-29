-- Prove2me | Definitions.Def_UnifiedMEstimator_General_L1Example
-- name    : UnifiedMEstimator_General_L1Example
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:12:34.557739+00:00
-- url     : https://prove2.me/theorems/cfd133b5-454b-40aa-a36d-42121d823f40
-- title:
--   The $\ell_1$-norm and the coordinate subspaces $\mathcal M(S)$ of Example 1
-- statement:
--   The sparse-vector setting of Example 1. On $\mathbb R^p$ with the Euclidean inner product and the $\ell_2$ error norm, the regularizer is the $\ell_1$-norm
--   $$\|\theta\|_1=\sum_{j=1}^p|\theta_j| ,$$
--   and for a subset $S\subseteq\{1,\dots,p\}$ the model subspace (Eq. (5)) is
--   $$\mathcal M(S)=\{\theta\in\mathbb R^p \mid \theta_j=0\ \text{for all } j\notin S\}.$$
--
--   These objects are the running example of the paper: the $\ell_1$-norm is decomposable over $(\mathcal M(S),\mathcal M^\perp(S))$, and the resulting bounds are the Lasso rates of Section 4.
--
--   **Formalization Note** $\mathbb R^p$ is `EuclideanSpace ℝ (Fin p)`, whose inner product is the Euclidean one; $\mathcal M(S)$ is a `Submodule`, with `S : Finset (Fin p)`.
-- source:
--   Negahban, Ravikumar, Wainwright and Yu, A Unified Framework for High-Dimensional Analysis of M-Estimators with Decomposable Regularizers, arXiv:1010.2731v3, pp. 4-5, Example 1, Eq. (5)

import Mathlib

namespace UnifiedMEstimator.General

/-!
The sparse-vector setting of Example 1 (Negahban, Ravikumar, Wainwright and Yu,
arXiv:1010.2731v3, p. 5): `ℝ^p` with the Euclidean error norm, the `ℓ₁`-norm regularizer, and
the coordinate model subspaces `M(S)` of Eq. (5).
-/

/-- The `ℓ₁`-norm `‖θ‖₁ = ∑_j |θ_j|` on `ℝ^p` (Example 1, p. 5). -/
noncomputable def l1Norm {p : ℕ} (θ : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ j, |θ j|

/-- The model subspace of Example 1 (p. 4, Eq. (5)): for `S ⊆ {1, …, p}`,
`M(S) := {θ ∈ ℝ^p | θ_j = 0 for all j ∉ S}`. -/
def coordSubspace {p : ℕ} (S : Finset (Fin p)) : Submodule ℝ (EuclideanSpace ℝ (Fin p)) where
  carrier := {θ | ∀ j, j ∉ S → θ j = 0}
  add_mem' := by
    intro a b ha hb j hj
    simp [ha j hj, hb j hj]
  zero_mem' := by
    intro j _
    simp
  smul_mem' := by
    intro c a ha j hj
    simp [ha j hj]

end UnifiedMEstimator.General


