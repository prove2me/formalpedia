-- Prove2me | Definitions.Def_LatentRobust_hStar
-- name    : LatentRobust_hStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:28.86474+00:00
-- url     : https://prove2.me/theorems/d43e6057-7f12-40b7-975a-8d18d05b9a89
-- title:
--   The Bayes-optimal classifier $h^*$ of the Gaussian mixture model (Corollary 2.3)
-- statement:
--   For the latent Gaussian mixture model (5) with parameters $W,\mu,\pi,\varphi$, let $q=\log\frac{1-\pi}{\pi}$ and define
--   $$
--   h^*(x)=\operatorname{sign}\Big(\varphi^{-1}(x)^\top\,(WW^\top)^\dagger\,W\mu-\frac q2\Big),
--   $$
--   where $\varphi^{-1}$ acts entrywise and $\dagger$ is the Moore–Penrose inverse.
--
--   Corollary 2.3 identifies this explicit formula as the Bayes-optimal classifier of the model, and Theorem 3.1 concerns its boundary risk.
--
--   **Formalization Note** $h^*$ is the formula on all of $\mathbb R^d$. $\varphi^{-1}$ is `Function.invFun φ`, the inverse of $\varphi$ under the standing assumption $\varphi'\ge c>0$; the sign is $\{\pm1\}$-valued with $\operatorname{sign}(0)=-1$. Statements using $q$ assume $0<\pi<1$.
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, Corollary 2.3, p.7 (and (18), p.21)

import Mathlib
import Definitions.Def_LatentRobust_sgn
import Definitions.Def_LatentRobust_pinv
import Definitions.Def_LatentRobust_gmmLaw

namespace LatentRobust

/-- The log-odds threshold `q = log((1 − π)/π)` of Corollary 2.3 (Javanmard, Mehrabi,
arXiv:2110.11950v2, p.7). Every theorem using it assumes `0 < π < 1`, where the logarithm's
argument is positive. -/
noncomputable def logOdds {d k : ℕ} (M : LatentGMM d k) : ℝ :=
  Real.log ((1 - M.π) / M.π)

/-- The Bayes-optimal classifier of the latent Gaussian mixture model (5), in the closed form of
Corollary 2.3 (Javanmard, Mehrabi, arXiv:2110.11950v2, p.7):
`h*(x) = sign( φ⁻¹(x)ᵀ (WWᵀ)† Wμ − q/2 )`, `q = log((1 − π)/π)`.

**Formalization Note** `h*` is this explicit formula on all of `ℝ^d` (it is not "some"
minimizer of the standard risk). `φ⁻¹` is `Function.invFun φ` applied entrywise; under the
standing assumption `φ' ≥ c > 0`, `φ` is a bijection of `ℝ` and `invFun φ` is its inverse. `†`
is the Moore–Penrose inverse `pinv`, and `sign` is `sgn` (`sgn 0 = −1`). -/
noncomputable def hStar {d k : ℕ} (M : LatentGMM d k) (x : Fin d → ℝ) : ℝ :=
  sgn ((fun i => Function.invFun M.φ (x i)) ⬝ᵥ
      ((pinv (M.W * M.W.transpose)).mulVec (M.W.mulVec M.μ)) - logOdds M / 2)

end LatentRobust


