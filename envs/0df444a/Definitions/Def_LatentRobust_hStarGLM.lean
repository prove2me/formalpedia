-- Prove2me | Definitions.Def_LatentRobust_hStarGLM
-- name    : LatentRobust_hStarGLM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:40.831826+00:00
-- url     : https://prove2.me/theorems/e317ac4a-61bf-44f5-aba2-2382c2d230ff
-- title:
--   The Bayes-optimal classifier of the generalized linear model (Corollary 2.3)
-- statement:
--   For the latent generalized linear model (6) with parameters $W,\beta,f,\varphi$, define
--   $$
--   h^*(x)=\operatorname{sign}\Big(f\big(\beta^\top(W^\top W)^{-1}W^\top\varphi^{-1}(x)\big)-\frac12\Big),
--   $$
--   where $\varphi^{-1}$ acts entrywise.
--
--   Corollary 2.3 identifies this formula as the Bayes-optimal classifier of model (6).
--
--   **Formalization Note** $\varphi^{-1}$ is `Function.invFun φ` (the inverse of $\varphi$ under $\varphi'\ge c>0$); $(W^\top W)^{-1}$ is the matrix inverse, a genuine inverse when $W$ has full column rank; the sign has $\operatorname{sign}(0)=-1$.
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, Corollary 2.3, p.7

import Mathlib
import Definitions.Def_LatentRobust_sgn
import Definitions.Def_LatentRobust_glmLaw

namespace LatentRobust

/-- The Bayes-optimal classifier of the latent generalized linear model (6), in the closed form
of Corollary 2.3 (Javanmard, Mehrabi, arXiv:2110.11950v2, p.7):
`h*(x) = sign( f( βᵀ (WᵀW)⁻¹ Wᵀ φ⁻¹(x) ) − 1/2 )`.

**Formalization Note** `φ⁻¹` is `Function.invFun φ` entrywise (the inverse of `φ` under the
standing assumption `φ' ≥ c > 0`); `(WᵀW)⁻¹` is Mathlib's matrix inverse, a genuine inverse
when `W` has full column rank; `sign` is `sgn` (`sgn 0 = −1`). -/
noncomputable def hStarGLM {d k : ℕ} (N : LatentGLM d k) (x : Fin d → ℝ) : ℝ :=
  sgn (N.f (N.β ⬝ᵥ ((N.W.transpose * N.W)⁻¹.mulVec
      (N.W.transpose.mulVec (fun i => Function.invFun N.φ (x i))))) - 1 / 2)

end LatentRobust


