-- Prove2me | Definitions.Def_ManIAL_psi
-- name    : ManIAL_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:16.817106+00:00
-- url     : https://prove2.me/theorems/5a9bad58-661e-4624-9acf-4a005254fc70
-- title:
--   Augmented Lagrangian $\psi(x)=\mathcal L_\sigma(x,z)$
-- statement:
--   For $\sigma>0$ and a multiplier $z\in\mathbb R^m$, the **augmented Lagrangian** of problem (1.1) after elimination of the auxiliary variable $y$ is
--
--   $$
--   \mathcal L_\sigma(x,z)=f(x)+M_h^{1/\sigma}\Big(\mathcal Ax-\frac1\sigma z\Big)-\frac1{2\sigma}\|z\|^2,
--   $$
--
--   where $M_h^{1/\sigma}(w)=\inf_{u}\{h(u)+\tfrac\sigma2\|u-w\|^2\}$ is the Moreau envelope of $h$ with parameter $1/\sigma$. ManIAL minimizes $\psi_k:=\mathcal L_{\sigma_k}(\cdot,z^k)$ over $\mathcal M$ in each outer iteration; unlike the augmented Lagrangian (3.5) in $(x,y)$ it is continuously differentiable in $x$.
--
--   **Formalization Note** The Moreau envelope is the published `BnBPEP.WeakCvx.moreauEnv` with parameter $\hat\rho=\sigma$, a real infimum; for the convex Lipschitz $h$ of the paper the infimum is finite and attained.
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, display (3.8), p.8; $\psi_k$, p.9

import Mathlib
import Definitions.Def_BnBPEP_WeakCvx_moreauEnv

open BnBPEP.WeakCvx

namespace ManIAL

/-- The augmented Lagrangian `ψ(x) = 𝓛_σ(x, z) = f(x) + M_h^{1/σ}(Ax − z/σ) − ‖z‖²/(2σ)`
(Deng–Hu–Wu–Wen, arXiv:2404.05121v2, display (3.8), p.8; `ψ_k(x) := 𝓛_{σ_k}(x, z^k)`, p.9).

**Formalization Note.** `M_h^{1/σ}(w) = inf_u {h(u) + (σ/2)‖u − w‖²}` is `moreauEnv σ h w`
(Definition 2.4, p.5, with `μ = 1/σ`). That real infimum is genuine for the convex Lipschitz `h`
of the paper (the objective is bounded below and its minimum is attained at the prox point). -/
noncomputable def psi {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (σ : ℝ)
    (z : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x + moreauEnv σ h (A x - σ⁻¹ • z) - ‖z‖ ^ 2 / (2 * σ)

end ManIAL


