-- Prove2me | Definitions.Def_RobustQueueRatio_SPStability_ChenS
-- name    : RobustQueueRatio_SPStability_ChenS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:44.009768+00:00
-- url     : https://prove2.me/theorems/ea61ee10-b873-4987-ad5c-7118f46e3af9
-- title:
--   S-matrices, completely-$\mathcal S$ matrices and the Chen-$\mathcal S$ condition on a pair $(R,\theta)$
-- statement:
--   This definition introduces the matrix conditions that govern existence and stability for the linear Skorohod problem $W(t)=W(0)+\theta t+RY(t)$.
--
--   **S-matrix.** A square matrix $R$ is an S-matrix if there is a vector $u$ with all entries positive such that $Ru$ also has all entries positive.
--
--   **Completely-$\mathcal S$.** A $J\times J$ matrix $R$ is completely-$\mathcal S$ if every principal sub-matrix $R_b=R_{bb}$, for nonempty $b\subseteq\{1,\dots,J\}$, is an S-matrix.
--
--   **Chen-$\mathcal S$.** For a $J\times J$ matrix $R$ and a vector $\theta\in\mathbb R^J$, the pair $(R,\theta)$ is Chen-$\mathcal S$ if $R$ is completely-$\mathcal S$ and there is a vector $h\in\mathbb R^J$ with all entries positive such that
--
--   $$
--   h_a^\top\,[\theta_a+R_{ab}u]<0
--   $$
--
--   for every partition $(a,b)$ of $\{1,\dots,J\}$ with $a\neq\emptyset$ and every $u\in\{v\in\mathbb R^{|b|}_+ : \theta_b+R_bv=0\}$. Here $u_a$, $\theta_a$ are sub-vectors and $R_{ab}$ is the sub-matrix with rows $a$ and columns $b$.
--
--   By Chen (1996), Chen-$\mathcal S$ of $(R,\theta)$ is a sufficient condition for stability of the Skorohod problem; completely-$\mathcal S$ of $R$ is necessary and sufficient for existence of its solutions.
--
--   **Formalization Note.** A partition $(a,b)$ is a `Finset` $a$ with $b=a^{\mathrm c}$; sub-vectors and sub-matrices are indexed by the subtypes of $a$ and $b$. The part $a$ must be nonempty, since for $a=\emptyset$ the left side is the empty sum $0$ and the condition would be unsatisfiable. The part $b$ may be empty, in which case $u$ is the empty vector and the condition reads $h^\top\theta<0$. The S-matrix predicate is stated over any finite index type, so that it applies to principal sub-matrices. The paper's Definition 5 fixes $R=(CMQ\Delta)^{-1}$ and $\theta=R(\rho-e)$. Here the predicate is stated for an arbitrary pair, and the theorems apply it to that pair.
-- source:
--   Zhao, Gurvich & Hasenbein, A Hierarchical Approach to Robust Stability of Multiclass Queueing Networks, arXiv:2303.17746v3, p. 10, Definition 4 (Completely-S) and Definition 5 (Chen-S), eq. (2.8)

import Mathlib

namespace RobustQueueRatio.SPStability

open Matrix

/-- A square matrix `R` is an **S-matrix** if there is a positive vector `u` (every entry `> 0`)
with `R u > 0` (every entry `> 0`) (Zhao, Gurvich & Hasenbein, arXiv:2303.17746v3, p. 10,
Definition 4). The index type is any finite type, so that principal sub-matrices, indexed by a
subset of the stations, are covered. -/
def IsSMatrix {ι : Type} [Fintype ι] (R : Matrix ι ι ℝ) : Prop :=
  ∃ u : ι → ℝ, (∀ i, 0 < u i) ∧ ∀ i, 0 < (R *ᵥ u) i

/-- A `J × J` matrix `R` is **completely-S** if each of its principal sub-matrices
`R_b = R_{bb}`, for every nonempty `b ⊆ {1, …, J}`, is an S-matrix (arXiv:2303.17746v3, p. 10,
Definition 4). The empty sub-matrix is excluded; it would be an S-matrix vacuously anyway. -/
def IsCompletelyS {J : ℕ} (R : Matrix (Fin J) (Fin J) ℝ) : Prop :=
  ∀ b : Finset (Fin J), b.Nonempty →
    IsSMatrix (R.submatrix (Subtype.val : b → Fin J) (Subtype.val : b → Fin J))

/-- The pair `(R, θ)` is **Chen-S** (arXiv:2303.17746v3, p. 10, Definition 5) if `R` is
completely-S and there is a positive vector `h ∈ ℝ^J` such that
`h_a′ [θ_a + R_{ab} u] < 0` (2.8) for every partition `(a, b)` of `{1, …, J}` and every
`u ∈ {v ∈ ℝ^{|b|}_+ : θ_b + R_b v = 0}`.

A partition is a subset `a` with `b = aᶜ`; `a` is required to be nonempty (for `a = ∅` the
left side of (2.8) is the empty sum `0`), while `b = ∅` is allowed (then `u` is the empty vector
and (2.8) reads `h′θ < 0`). In Definition 5 `R` and `θ` are the network's `(CMQΔ)⁻¹` and
`R(ρ − e)`; this predicate is stated for an arbitrary pair and is applied to those. -/
def IsChenS {J : ℕ} (R : Matrix (Fin J) (Fin J) ℝ) (θ : Fin J → ℝ) : Prop :=
  IsCompletelyS R ∧
    ∃ h : Fin J → ℝ, (∀ j, 0 < h j) ∧
      ∀ a : Finset (Fin J), a.Nonempty →
        ∀ u : (aᶜ : Finset (Fin J)) → ℝ, (∀ i, 0 ≤ u i) →
          (∀ i : (aᶜ : Finset (Fin J)),
              θ i + (R.submatrix (Subtype.val : (aᶜ : Finset (Fin J)) → Fin J)
                (Subtype.val : (aᶜ : Finset (Fin J)) → Fin J) *ᵥ u) i = 0) →
          ∑ i : a, h i * (θ i + (R.submatrix (Subtype.val : a → Fin J)
                (Subtype.val : (aᶜ : Finset (Fin J)) → Fin J) *ᵥ u) i) < 0

end RobustQueueRatio.SPStability


