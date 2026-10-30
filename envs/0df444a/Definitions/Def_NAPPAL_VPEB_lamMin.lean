-- Prove2me | Definitions.Def_NAPPAL_VPEB_lamMin
-- name    : NAPPAL_VPEB_lamMin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:03:27.431595+00:00
-- url     : https://prove2.me/theorems/d9062213-6020-46bb-a8a2-67462479c289
-- title:
--   $\lambda_{\min}(B^\top B)$ as a Rayleigh infimum
-- statement:
--   For a linear map $B : \mathbb{R}^d \to \mathbb{R}^m$ (an $m \times d$ matrix),
--   $$\lambda_{\min}(B^\top B) = \inf_{\|x\| = 1} \|Bx\|^2 ,$$
--   the smallest eigenvalue of the positive semidefinite matrix $B^\top B$ (Rayleigh–Ritz). It is positive exactly when $B$ has full column rank.
--
--   It enters the penalty threshold of Assumption 2(ii), the step bound (8), and the constants of Lemmas 4.1–4.3.
--
--   **Formalization Note** For $d = 0$ the unit sphere is empty and Lean's real infimum is $0$; the mission always assumes $\lambda_{\min}(B^\top B) > 0$, which excludes that case.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, §2, p. 5 (λmin(A) is the minimum eigenvalue)

import Mathlib

namespace NAPPAL.VPEB

/-- **`λ_min(BᵀB)`, the smallest eigenvalue of `BᵀB`.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, §2, p. 5: "For a matrix A, the minimum eigenvalue is denoted by λmin(A)." It enters through
`λmin(B⊤B)` in Assumption 2(ii) (p. 9), (8) (p. 9) and Lemmas 4.1–4.3.

`lamMin B = inf_{‖x‖ = 1} ‖Bx‖²`, the Rayleigh quotient infimum of `BᵀB` over the unit sphere
of `ℝᵈ`.

**Formalization Note.** For `d ≥ 1` this infimum is the smallest eigenvalue of the positive
semidefinite matrix `BᵀB` (Rayleigh–Ritz). For `d = 0` the sphere is empty and Lean's real `⨅`
returns `0`; every statement of the mission assumes `0 < lamMin B` (full column rank of `B`),
which excludes that case. -/
noncomputable def lamMin {d m : ℕ}
    (B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m)) : ℝ :=
  ⨅ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, ‖B x‖ ^ 2

end NAPPAL.VPEB


