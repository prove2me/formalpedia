-- Prove2me | Definitions.Def_AdaptiveCubic_SecondOrder_lamMin
-- name    : AdaptiveCubic_SecondOrder_lamMin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:21.992982+00:00
-- url     : https://prove2.me/theorems/aec2f81e-0949-4779-97f8-aca2d2906b89
-- title:
--   Leftmost eigenvalue λ_min(QᵀBQ) of the compression of B to a subspace
-- statement:
--   Let $B$ be a symmetric operator on $\mathbb R^n$ and $\mathcal L\subseteq\mathbb R^n$ a subspace, and let $Q$ be any matrix with orthonormal columns forming a basis of $\mathcal L$. The **leftmost eigenvalue of the compression** $Q^\top BQ$ is
--
--   $$\lambda_{\min}(Q^\top BQ) = \min\{\,v^\top Bv \;:\; v\in\mathcal L,\ \|v\|=1\,\}.$$
--
--   By the Courant–Fischer theorem (with $v=Qy$) the right-hand side does not depend on the choice of $Q$. The quantity measures the curvature of the model's quadratic part inside the subspace $\mathcal L_k$ where ARC(S) minimizes; $-\lambda_{\min}(Q_k^\top B_kQ_k)\le\epsilon$ is the approximate second-order criticality measure of Corollary 5.4.
--
--   **Formalization Note** The definition is the Rayleigh-quotient infimum over unit vectors of $\mathcal L$, not the eigenvalue of $B$ on all of $\mathbb R^n$. The quadratic form is bounded below by $-\|B\|$ on the unit sphere, so for $\mathcal L\ne\{0\}$ the infimum is attained and is a genuine minimum. For $\mathcal L=\{0\}$ ($Q$ with no columns) the index set is empty and Lean's real infimum returns $0$, so $-\lambda_{\min}>\epsilon$ never holds there.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 16, Corollary 5.4

import Mathlib

open scoped RealInnerProductSpace

namespace AdaptiveCubic.SecondOrder

/-- The leftmost eigenvalue `λ_min(Qᵀ B Q)` of the compression of `B` to a subspace `L` of `ℝⁿ`
(Cartis, Gould & Toint, *Adaptive cubic regularisation methods for unconstrained optimization.
Part II*, preprint rev. 15 Sep 2009, p. 16, Corollary 5.4), written as the Rayleigh-quotient infimum
`min { vᵀ B v : v ∈ L, ‖v‖ = 1 }`. For symmetric `B` and any `Q` whose orthonormal columns span `L`
this is `λ_min(Qᵀ B Q)` (Courant–Fischer, with `v = Q y`), independently of the choice of `Q`. The
quadratic form is bounded below by `−‖B‖` on the unit sphere, so for `L ≠ ⊥` this is a genuine
minimum; for `L = ⊥` (no columns) the index set is empty and Lean's real `⨅` returns `0`. -/
noncomputable def lamMin {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ⨅ v : {v : EuclideanSpace ℝ (Fin n) // v ∈ L ∧ ‖v‖ = 1}, ⟪B v, v⟫

end AdaptiveCubic.SecondOrder


