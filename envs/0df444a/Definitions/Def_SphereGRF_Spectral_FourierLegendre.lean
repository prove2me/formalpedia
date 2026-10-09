-- Prove2me | Definitions.Def_SphereGRF_Spectral_FourierLegendre
-- name    : SphereGRF_Spectral_FourierLegendre
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:05.068326+00:00
-- url     : https://prove2.me/theorems/a47a9bbb-c3d5-4191-a970-ce4815b05712
-- title:
--   §3, pp. 10–11 — Fourier–Legendre coefficients $u_\ell$ and the weighted sum $\sum u_\ell^2 \frac{2\ell+1}{2}(1+\ell^{2\eta})$
-- statement:
--   For $u \in L^2(-1,1)$ and $\ell \in \mathbb N_0$ the **Fourier–Legendre coefficient** of $u$ is
--
--   $$
--   u_\ell = \int_{-1}^1 u(x)\,P_\ell(x)\,dx ,
--   $$
--
--   so that $u = \sum_{\ell \ge 0} u_\ell \frac{2\ell+1}{2} P_\ell$ in $L^2(-1,1)$. For $\eta \ge 0$ the weights of the sequence space $\ell_\eta$ are $\frac{2\ell+1}{2}(1 + \ell^{2\eta})$, and the weighted sum is
--
--   $$
--   \sum_{\ell=0}^\infty u_\ell^2\,\frac{2\ell+1}{2}\,(1+\ell^{2\eta}) \in [0,+\infty].
--   $$
--
--   Theorem 3.1 of the paper characterises membership in $V^\eta(-1,1)$ by finiteness of this sum.
--
--   **Formalization Note** $\ell^{2\eta}$ is the real power with the convention $0^0 = 1$, so the $\ell = 0$ weight is $1$ for $\eta = 0$ and $1/2$ for $\eta > 0$. The sum is taken in $[0, +\infty]$.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §3, p. 10 (u_ℓ, ℓ_n), Theorem 3.1, p. 11

import Mathlib
import Definitions.Def_SphereGRF_Spectral_Legendre

open scoped ENNReal

namespace SphereGRF.Spectral

/-- The Fourier–Legendre coefficient `u_ℓ = ∫_{−1}^1 u(x) P_ℓ(x) dx` (p. 10). -/
noncomputable def legendreCoeff (u : ℝ → ℝ) (ℓ : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, u x * (legendreP ℓ).eval x

/-- The weight `(2ℓ+1)/2 · (1 + ℓ^{2η})` of the sequence space `ℓ_η` (p. 10), with the real power
`ℓ^{2η}` (`0^0 = 1`). -/
noncomputable def specWeight (η : ℝ) (ℓ : ℕ) : ℝ :=
  (2 * (ℓ : ℝ) + 1) / 2 * (1 + (ℓ : ℝ) ^ (2 * η))

/-- `Σ_{ℓ ≥ 0} u_ℓ² (2ℓ+1)/2 (1 + ℓ^{2η})`, in `[0, ∞]` (Theorem 3.1, p. 11). -/
noncomputable def specWeightSum (η : ℝ) (u : ℝ → ℝ) : ℝ≥0∞ :=
  ∑' ℓ : ℕ, ENNReal.ofReal (legendreCoeff u ℓ ^ 2 * specWeight η ℓ)

end SphereGRF.Spectral


