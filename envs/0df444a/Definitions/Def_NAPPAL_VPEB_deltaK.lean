-- Prove2me | Definitions.Def_NAPPAL_VPEB_deltaK
-- name    : NAPPAL_VPEB_deltaK
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:10:51.856381+00:00
-- url     : https://prove2.me/theorems/de4d514e-50fb-431e-9a62-b7b51bc2f433
-- title:
--   The step bound $\delta_k$ of (8)
-- statement:
--   For a sequence $w^k$, set
--   $$\delta_k = \beta \left( L_G + \|q^k\| L_\Omega + \gamma (L^0_\Theta)^2 + \frac{14\gamma\|B\|^2 (L^0_\Theta)^2}{\lambda_{\min}(B^\top B)} + \frac{14(L_G + \gamma\|B\|L^0_\Theta)^2}{\gamma\lambda_{\min}(B^\top B)} + 1 \right)^{-1},$$
--   where $L_\Omega = \sum_j L_{\Omega_j}$ and $\|B\|$ is the spectral norm. NAPP-AL chooses $\epsilon^k \in [\sigma\delta_k, \delta_k]$.
--
--   **Formalization Note** $\|B\|$ is the operator norm of $B$ between Euclidean spaces, which is the spectral norm.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, Proposition 3.1, p. 9, eq. (8)

import Mathlib
import Definitions.Def_NAPPAL_VPEB_W
import Definitions.Def_NAPPAL_VPEB_lamMin
import Definitions.Def_NAPPAL_VPEB_Problem
import Definitions.Def_NAPPAL_VPEB_Params
import Definitions.Def_NAPPAL_VPEB_qk

namespace NAPPAL.VPEB

/-- **The step bound `δ_k` of (8).**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, Proposition 3.1, p. 9, eq. (8): "δk := β(LG + ‖q^k‖LΩ + γ(L0Θ)² + 14γ‖B‖²(L0Θ)²/λmin(B⊤B)
+ 14(LG + γ‖B‖L0Θ)²/(γλmin(B⊤B)) + 1)^{−1}."

`deltaK P A w k = β / (L_G + ‖q^k‖ L_Ω + γ(L⁰_Θ)² + 14γ‖B‖²(L⁰_Θ)²/λ_min(BᵀB)
+ 14(L_G + γ‖B‖L⁰_Θ)²/(γλ_min(BᵀB)) + 1)`, where `L_Ω = Σ_j L_{Ω_j}` ((H5), p. 7).

**Formalization Note.** `‖B‖` is the operator norm of `B : ℝᵈ → ℝᵐ` with Euclidean norms, i.e.
the spectral norm (p. 5). Under Assumptions 1–2 the denominator is at least `1`. -/
noncomputable def deltaK {n d m : ℕ} (P : Problem n d m) (A : Params n) (w : ℕ → W n d m)
    (k : ℕ) : ℝ :=
  A.β / (P.LG + ‖qk P A w k‖ * (∑ j, P.LΩj j) + A.γ * P.L0Θ ^ 2 +
    14 * A.γ * ‖P.B‖ ^ 2 * P.L0Θ ^ 2 / lamMin P.B +
    14 * (P.LG + A.γ * ‖P.B‖ * P.L0Θ) ^ 2 / (A.γ * lamMin P.B) + 1)

end NAPPAL.VPEB


