-- Prove2me | Definitions.Def_FermionModewise_pairBlock
-- name    : FermionModewise_pairBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:25.92965+00:00
-- url     : https://prove2.me/theorems/67753f75-1bfe-4b8d-a415-8a172b6f2d82
-- title:
--   The two-mode covariance block (12)
-- statement:
--   For real $\lambda,\kappa$, the $4\times4$ real matrix of (12), in the quadrature order $\tilde A_1,\tilde A_2,\tilde B_1,\tilde B_2$:
--   $$\widetilde M_{\tilde A\tilde B}=\begin{pmatrix}0&-\lambda&0&\kappa\\\lambda&0&\kappa&0\\0&-\kappa&0&-\lambda\\-\kappa&0&\lambda&0\end{pmatrix}.$$
--   With $\kappa^2+\lambda^2=\lambda_0^2$ it is the covariance matrix of an entangled pair in the isotropic normal form (11)–(12). At $\lambda_0=1$ it is the FCM of the two-mode squeezed state $\cos\theta|00\rangle-\sin\theta|11\rangle$ with $\lambda=\cos2\theta$, $\kappa=\sin2\theta$ (milestone `two_mode_squeezed`).
--
--   **Formalization Note.** The index is (mode, quadrature) $\in\{0,1\}\times\{0,1\}$, mode $0$ being $\tilde A$ and mode $1$ being $\tilde B$, matching the quadratures of the pair $(a,b)$. The relation $\kappa^2+\lambda^2=\lambda_0^2$ is not built in.
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (12), p.6

import Mathlib

open Matrix

namespace FermionModewise

/-- **Two-mode block (12)** (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (12), p.6): the `4 × 4`
covariance matrix of an entangled pair `(Ã_i, B̃_i)`,
```
⎛  0  −λ   0   κ ⎞
⎜  λ   0   κ   0 ⎟
⎜  0  −κ   0  −λ ⎟
⎝ −κ   0   λ   0 ⎠
```
in the quadrature order `A₁ A₂ B₁ B₂`.

**Formalization Note.** The index is `Fin 2 × Fin 2` = (mode, quadrature), mode `0` = `Ã_i`,
mode `1` = `B̃_i`, matching `majorana ![a, b]`. `finProdFinEquiv` sends `(m, x)` to `2m + x`,
so the order is `(0,0), (0,1), (1,0), (1,1)` = `A₁ A₂ B₁ B₂`. The relation `κ² + λ² = λ₀²` is
not built in. -/
def pairBlock (lam kap : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  (!![0, -lam, 0, kap;
      lam, 0, kap, 0;
      0, -kap, 0, -lam;
      -kap, 0, lam, 0] : Matrix (Fin 4) (Fin 4) ℝ).submatrix finProdFinEquiv finProdFinEquiv

end FermionModewise


