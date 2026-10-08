-- Prove2me | Definitions.Def_RWPI_SqrtLasso_Nq
-- name    : RWPI_SqrtLasso_Nq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:28:31.681231+00:00
-- url     : https://prove2.me/theorems/ebafd556-314c-4a98-ad03-7e83f33e1766
-- title:
--   Modified norm cost $N_q$ that forbids moving the response (Eq. (14))
-- statement:
--   For $q\in[1,\infty]$ and predictor–response pairs $(x,y),(u,v)\in\mathbb R^d\times\mathbb R$, define
--
--   $$
--   N_q\big((x,y),(u,v)\big) = \begin{cases} \|x-u\|_q, & \text{if } y = v,\\ +\infty, & \text{otherwise}, \end{cases}
--   $$
--
--   where $\|\cdot\|_q$ is the $\ell_q$ norm on $\mathbb R^d$. Used as a transport cost (or through its powers $N_q^\rho$), it assigns infinite cost to any change of the response, so every probability measure at finite transport cost from the empirical distribution $P_n$ has the same response marginal as $P_n$: the ambiguity is only in the predictors. With $\rho = 2$ it yields Theorem 1, with $\rho = 1$ the classification results of Theorem 2.
--
--   **Formalization Note** The value is in $[0,\infty]$ (`ENNReal`), $+\infty$ being `⊤`; the norm is that of `PiLp q`, with $q = \infty$ the max norm. $N_q$ vanishes on the diagonal and is lower semicontinuous.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 11, Eq. (14)

import Mathlib

namespace RWPI.SqrtLasso

/-- The modified norm cost `N_q` of Eq. (14), p. 11, on predictor–response pairs
`(x, y) ∈ ℝ^d × ℝ`:
`N_q((x, y), (u, v)) = ‖x − u‖_q` if `y = v`, and `+∞` otherwise.
The exponent `q ∈ [1, ∞]` is an extended real; `‖·‖_q` is the `ℓ_q` norm of `ℝ^d`
(`PiLp q`), with `q = ∞` the max norm. -/
noncomputable def Nq {d : ℕ} (q : ENNReal) (z w : (Fin d → ℝ) × ℝ) : ENNReal :=
  if z.2 = w.2 then ENNReal.ofReal ‖WithLp.toLp q (z.1 - w.1)‖ else ⊤

end RWPI.SqrtLasso


