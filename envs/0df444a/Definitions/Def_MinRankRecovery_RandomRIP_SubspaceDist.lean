-- Prove2me | Definitions.Def_MinRankRecovery_RandomRIP_SubspaceDist
-- name    : MinRankRecovery_RandomRIP_SubspaceDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:48.338988+00:00
-- url     : https://prove2.me/theorems/771af93b-cca1-40f6-9ff4-63d75ff40bda
-- title:
--   (4.10) and p. 17 — the projection distance $\rho(T_1,T_2)$ and the subspace $\Sigma(V,W)$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space. For subspaces $T_1,T_2\subseteq E$ with orthogonal projections $P_{T_1},P_{T_2}$, the **projection distance** is
--   $$\rho(T_1,T_2) := \|P_{T_1}-P_{T_2}\|,$$
--   the operator norm of the difference of the projections. It equals the sine of the largest principal angle between $T_1$ and $T_2$, and it is the metric with which the paper equips the Grassmannian.
--
--   For subspaces $V\subseteq\mathbb R^m$ and $W\subseteq\mathbb R^n$, $\Sigma(V,W)\subseteq\mathbb R^{m\times n}$ is the subspace of all $m\times n$ matrices whose column space is contained in $V$ and whose row space is contained in $W$; equivalently, every column of $X$ lies in $V$ and every row of $X$ lies in $W$. When $\dim V=\dim W=r$, $\Sigma(V,W)$ has dimension $r^2$ and consists of matrices of rank at most $r$, and every matrix of rank at most $r$ lies in some such $\Sigma(V,W)$.
--
--   These two objects let the paper cover the set of low-rank matrices by finitely many subspaces.
--
--   **Formalization Note** Matrices are identified with their vectorizations in $\mathbb R^{mn}$ (the paper's $\operatorname{vec}$, (4.4)), realised as `EuclideanSpace ℝ (Fin m × Fin n)`, whose inner product is the Frobenius inner product; entry $(i,j)$ of the vector is the matrix entry $X_{ij}$. Orthogonal projections are Mathlib's `Submodule.starProjection`, and $\rho$ is the norm of their difference as continuous linear maps.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, (4.10), p. 16; definition of Σ(V, W), p. 17

import Mathlib

namespace MinRankRecovery.RandomRIP

/-- (4.10), p. 16: the distance `ρ(T₁, T₂) := ‖P_{T₁} − P_{T₂}‖` between two subspaces of a
finite-dimensional real inner product space, the operator norm of the difference of the
orthogonal projections onto them. -/
noncomputable def projDist {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T₁ T₂ : Submodule ℝ E) : ℝ :=
  ‖T₁.starProjection - T₂.starProjection‖

/-- p. 17: `Σ(V, W)`, for subspaces `V ⊆ ℝᵐ` and `W ⊆ ℝⁿ`, the subspace of `m × n` matrices
whose column space is contained in `V` and whose row space is contained in `W`. Matrices are
identified with their vectorizations in `EuclideanSpace ℝ (Fin m × Fin n)` (entry `(i, j)` of
`x` is the matrix entry `X i j`), which carries the Frobenius inner product: every column
`j ↦ (i ↦ x (i, j))` lies in `V` and every row `i ↦ (j ↦ x (i, j))` lies in `W`. -/
def sigmaSub {m n : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin n)) where
  carrier := {x | (∀ j, (WithLp.toLp 2 fun i => x (i, j)) ∈ V) ∧
    (∀ i, (WithLp.toLp 2 fun j => x (i, j)) ∈ W)}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun j => ?_, fun i => ?_⟩
    · have := V.add_mem (ha.1 j) (hb.1 j)
      convert this using 1; ext; simp
    · have := W.add_mem (ha.2 i) (hb.2 i)
      convert this using 1; ext; simp
  zero_mem' := by
    refine ⟨fun j => ?_, fun i => ?_⟩
    · convert V.zero_mem using 1; ext; simp
    · convert W.zero_mem using 1; ext; simp
  smul_mem' := by
    intro c a ha
    refine ⟨fun j => ?_, fun i => ?_⟩
    · convert V.smul_mem c (ha.1 j) using 1; ext; simp
    · convert W.smul_mem c (ha.2 i) using 1; ext; simp

end MinRankRecovery.RandomRIP


