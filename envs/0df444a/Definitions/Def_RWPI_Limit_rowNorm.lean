-- Prove2me | Definitions.Def_RWPI_Limit_rowNorm
-- name    : RWPI_Limit_rowNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:50:38.66953+00:00
-- url     : https://prove2.me/theorems/c73c340f-21e7-410f-b77c-ee5cd8af598d
-- title:
--   The dual norm $\|\zeta^T D_w h(w, \theta)\|_p$ of a row of the Jacobian
-- statement:
--   Let $h : \mathbb R^m \times \mathbb R^l \to \mathbb R^r$, $\theta \in \mathbb R^l$, and let $D_w h(w, \theta)$ be the $r \times m$ Jacobian matrix of $w \mapsto h(w, \theta)$ at $w$, with entries $\partial h_j / \partial w_k$. For $\zeta \in \mathbb R^r$ the row vector $\zeta^T D_w h(w, \theta) \in \mathbb R^m$ has $k$-th entry $\sum_{j=1}^r \zeta_j \, \partial h_j(w, \theta)/\partial w_k$. For $p \in [1, \infty]$ this file defines
--
--   $$
--   \|\zeta^T D_w h(w, \theta)\|_p ,
--   $$
--
--   its $\ell_p$ norm. In the paper $p$ is the exponent conjugate to the cost's $q$ ($1/p + 1/q = 1$), so this is the dual norm that measures how fast $\zeta^T h(\cdot, \theta)$ can grow per unit of transport. It appears in Assumption A4) and in the limit $\bar R(\rho)$ of Theorem 3.
--
--   **Formalization Note.** The partial derivative $\partial h_j/\partial w_k$ is the $j$-th component of the Fréchet derivative of $w \mapsto h(w,\theta)$ applied to the $k$-th standard basis vector, and the norm is Mathlib's `PiLp p` norm.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 15, Assumption A4), Eq. (21)

import Mathlib

namespace RWPI.Limit

/-- `‖ζ^T D_w h(w, θ)‖_p` (Assumption A4), p. 15): `D_w h(w, θ)` is the `r × m` Jacobian of
`w ↦ h(w, θ)` at `w`, with entries `∂h_j/∂w_k = (fderiv ℝ (h · θ) w (e_k))_j`; the row vector
`ζ^T D_w h(w, θ) ∈ ℝ^m` has `k`-th entry `Σ_j ζ_j ∂h_j/∂w_k`, and its `ℓ_p` norm is taken through
`PiLp p`. -/
noncomputable def rowNorm {m l r : ℕ} (p : ENNReal)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θ : Fin l → ℝ)
    (ζ : Fin r → ℝ) (w : Fin m → ℝ) : ℝ :=
  ‖WithLp.toLp p (fun k : Fin m => ∑ j, ζ j * fderiv ℝ (fun x => h x θ) w (Pi.single k 1) j)‖

end RWPI.Limit


