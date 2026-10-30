-- Prove2me | Definitions.Def_NAPPAL_VPEB_Params
-- name    : NAPPAL_VPEB_Params
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:06:23.661112+00:00
-- url     : https://prove2.me/theorems/a69c8c22-7e45-40d0-86fc-a402a01ffaa5
-- title:
--   The parameters $K, \beta, L_K, \gamma, \sigma$ of NAPP-AL
-- statement:
--   The **parameters** of NAPP-AL are the kernel $K : \mathbb{R}^n \to \mathbb{R}$ of the Bregman distance, its strong convexity modulus $\beta$, the Lipschitz constant $L_K$ of $\nabla K$, the penalty parameter $\gamma$ and the safeguard $\sigma$ used in choosing the step parameters $\epsilon^k$. Their hypotheses (Assumption 2) are a separate definition.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, §3, p. 8 (Bregman distance; NAPP-AL box: Parameters)

import Mathlib

namespace NAPPAL.VPEB

/-- **The algorithm parameters of NAPP-AL: the Bregman kernel `K`, `β`, `L_K`, `γ`, `σ`.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, §3, p. 8: "let us introduce a Bregman distance function D(u, u′) = K(u) − K(u′) −
⟨∇K(u′), u − u′⟩ where K is β-strongly convex and LK-gradient Lipschitz", and the NAPP-AL box:
"Parameters: L0Θ, LΩ, LH, LG, and γ > 0, β, 0 < σ < 1".

A `Params n` records `K : ℝⁿ → ℝ` and the numbers `β`, `L_K`, `γ`, `σ`. The hypotheses on them
(Assumption 2 and the box) are `Assumption2`. -/
structure Params (n : ℕ) where
  /-- the kernel `K` of the Bregman distance -/
  K : EuclideanSpace ℝ (Fin n) → ℝ
  /-- the strong convexity modulus `β` of `K` -/
  β : ℝ
  /-- the Lipschitz constant `L_K` of `∇K` -/
  LK : ℝ
  /-- the penalty parameter `γ` -/
  γ : ℝ
  /-- the step-size safeguard `σ ∈ (0, 1)` -/
  σ : ℝ

end NAPPAL.VPEB


