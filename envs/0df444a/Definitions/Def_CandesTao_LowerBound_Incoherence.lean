-- Prove2me | Definitions.Def_CandesTao_LowerBound_Incoherence
-- name    : CandesTao_LowerBound_Incoherence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:43:35.867828+00:00
-- url     : https://prove2.me/theorems/dc4d11c7-dcd1-4007-a934-1938a2f174b0
-- title:
--   Rank at most r with the incoherence property of parameter μ₀ (I.18)
-- statement:
--   Let $M \in \mathbb{R}^{n_1\times n_2}$. Write $U \subseteq \mathbb{R}^{n_1}$ for its column space (the range of $x \mapsto Mx$) and $V \subseteq \mathbb{R}^{n_2}$ for its row space (the range of $y \mapsto M^{\top}y$), and let $P_U$, $P_V$ be the orthogonal projections onto them. Let $e_a$ denote the $a$-th standard basis vector.
--
--   Given an integer $r$ and a real $\mu_0$, the matrix $M$ **has rank at most $r$ and obeys the incoherence property with parameter $\mu_0$** if $\operatorname{rank} M \le r$ and
--
--   $$\|P_U e_a\|^2 \le \frac{\mu_0 r}{n_1}\quad\text{for all } a\in[n_1], \qquad \|P_V e_b\|^2 \le \frac{\mu_0 r}{n_2}\quad\text{for all } b\in[n_2].$$
--
--   Incoherence says that no standard basis vector is well aligned with the column or row space, so the information in $M$ is spread over many entries. This is the class of matrices in the lower bound of Candès and Tao (Theorem 1.7): "rank at most $r$ and obeying the incoherence property (I.18) with parameter $\mu_0$".
--
--   **Formalization Note** The bound uses the rank bound $r$ of the theorem, not $\operatorname{rank} M$, as Theorem 1.7 applies (I.18) to matrices of rank at most $r$. The projections are Mathlib's orthogonal projections (`Submodule.starProjection`) onto `LinearMap.range (Matrix.toEuclideanLin M)` and the same for $M^{\top}$ in `EuclideanSpace ℝ (Fin n)`, and the norm is the Euclidean norm. The platform predicate `A0` is not used because it requires an exact rank-$r$ SVD and divides by that rank.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2057, Eq. (I.18) (incoherence property with parameter μ₀), as applied to matrices of rank at most r in Theorem 1.7, p. 2058

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

namespace CandesTao.LowerBound

/-- The column space `U ⊆ ℝ^{n₁}` of `M`: the range of `x ↦ M x`. -/
noncomputable def columnSpace {n1 n2 : ℕ} (M : RealMatrix n1 n2) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n1)) :=
  LinearMap.range (Matrix.toEuclideanLin M)

/-- The row space `V ⊆ ℝ^{n₂}` of `M`: the range of `y ↦ Mᵀ y`. -/
noncomputable def rowSpace {n1 n2 : ℕ} (M : RealMatrix n1 n2) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n2)) :=
  LinearMap.range (Matrix.toEuclideanLin M.transpose)

/-- Candès–Tao (I.18), as used in Theorem 1.7: `M` has rank at most `r` and obeys
the incoherence property with parameter `μ₀`, i.e. for all `a ∈ [n₁]`, `b ∈ [n₂]`,
`‖P_U e_a‖² ≤ μ₀ r / n₁` and `‖P_V e_b‖² ≤ μ₀ r / n₂`, where `P_U`, `P_V` are the
orthogonal projections onto the column and row spaces of `M`, and `r` is the
rank bound of the theorem (not `rank M`). -/
def IncoherentRankAtMost {n1 n2 : ℕ} (r : ℕ) (μ₀ : ℝ) (M : RealMatrix n1 n2) : Prop :=
  M.rank ≤ r ∧
  (∀ a : Fin n1,
    ‖(columnSpace M).starProjection (EuclideanSpace.single a (1 : ℝ))‖ ^ 2 ≤
      μ₀ * r / n1) ∧
  (∀ b : Fin n2,
    ‖(rowSpace M).starProjection (EuclideanSpace.single b (1 : ℝ))‖ ^ 2 ≤
      μ₀ * r / n2)

end CandesTao.LowerBound


