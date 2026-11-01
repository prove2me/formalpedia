-- Prove2me | Definitions.Def_ManIAL_Lk
-- name    : ManIAL_Lk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:01.645308+00:00
-- url     : https://prove2.me/theorems/5ebc5938-57e3-4c2d-8ded-ad92f2020662
-- title:
--   Smoothness constant $L_k=\alpha^2(\ell_{\nabla f}+\sigma_k\|\mathcal A\|^2)+2G\beta$
-- statement:
--   The constant
--
--   $$
--   L=\alpha^2\big(\ell_{\nabla f}+\sigma\|\mathcal A\|^2\big)+2G\beta
--   $$
--
--   is the retraction-smoothness constant of the subproblem objective $\psi=\mathcal L_\sigma(\cdot,z)$ (Lemma 3.3): $\ell_{\nabla f}+\sigma\|\mathcal A\|^2$ is the Lipschitz constant of $\nabla\psi$, $\alpha,\beta$ are the retraction constants of (2.1), and $G$ bounds $\|\nabla\psi\|$ on $\mathcal M$. With $\sigma=\sigma_k$ it is the inverse stepsize $L_k$ of Algorithm 2 inside ManIAL.
--
--   **Formalization Note** $\|\mathcal A\|$ is the operator norm.
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Lemma 3.3, p.11

import Mathlib

namespace ManIAL

/-- The retraction-smoothness constant of the subproblem, `L_k = α²(ℓ_{∇f} + σ_k‖A‖²) + 2Gβ`
(Deng–Hu–Wu–Wen, arXiv:2404.05121v2, Lemma 3.3, p.11), as a function of `σ = σ_k`.

**Formalization Note.** `‖A‖` is the operator norm; `α, β` are the constants of (2.1) and `G`
bounds `‖∇ψ_k‖` on `M`. -/
noncomputable def Lk {n m : ℕ} (α β G ℓf : ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (σ : ℝ) : ℝ :=
  α ^ 2 * (ℓf + σ * ‖A‖ ^ 2) + 2 * G * β

end ManIAL


