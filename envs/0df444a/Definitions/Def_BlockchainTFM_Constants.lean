-- Prove2me | Definitions.Def_BlockchainTFM_Constants
-- name    : BlockchainTFM_Constants
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:03.327126+00:00
-- url     : https://prove2.me/theorems/d4619a50-899c-415c-b21c-415d2bd33622
-- title:
--   The parameter $m_\#(\lambda_0)$, the constant $g(\lambda_0)$ and the $h$-range of Theorem 4
-- statement:
--   For $\lambda_0>e/(e-1)\approx1.582$ Theorem 4 uses the following constants.
--
--   1. **Logit parameter** (Theorem 4, (EC.115)):
--   $$m_\#(\lambda_0)=\min\Bigl\{\tfrac12\ln\frac{1}{\ln\frac{\lambda_0}{\lambda_0-1}},\,1\Bigr\}.$$
--   2. **The constant $g$** (Theorem 4):
--   $$g(\lambda_0)=\frac{m\cdot\max\Bigl\{1-\sqrt{\ln\frac{\lambda_0}{\lambda_0-1}},\ 1-e\ln\frac{\lambda_0}{\lambda_0-1}\Bigr\}}{e^{\,m-1+\frac{e}{0.9\lambda_0-1}}},\qquad m=m_\#(\lambda_0).$$
--   3. **Upper end of the $h$-range** (Theorem 4, (EC.136)): for block size $k$, $n$ users and constant $c$,
--   $$h_{\max}=g(\lambda_0)\,\frac{2kc(n-1)}{en^2}.$$
--
--   For $\lambda_0>e/(e-1)$ one has $\ln\frac{\lambda_0}{\lambda_0-1}<1$, so $m_\#(\lambda_0)>0$ and $g(\lambda_0)>0$; Theorem 4 (B) asserts UIR and BF for every $h\in[0,h_{\max}]$ with $c=c_\rho$.
--
--   **Formalization Note** All quantities are real numbers; $k$ and $n$ enter through their real casts. The definitions are total; their meaning matters only for $\lambda_0>e/(e-1)$.
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, Theorem 4 p.30; (EC.115)–(EC.116) p.ec21; (EC.132), (EC.136) p.ec23

import Mathlib

namespace BlockchainTFM

/-- **The logit parameter `m_#(λ₀)`**, arXiv:2209.13099v7, Theorem 4, p.30 (and (EC.115),
p.ec21): `m = min{ ½ ln (1 / ln(λ₀/(λ₀−1))), 1 }`. -/
noncomputable def mSharp (lam0 : ℝ) : ℝ :=
  min ((1 / 2) * Real.log (1 / Real.log (lam0 / (lam0 - 1)))) 1

/-- **The constant `g(λ₀)`**, arXiv:2209.13099v7, Theorem 4, p.30:
`g(λ₀) = m · max{1 − √(ln(λ₀/(λ₀−1))), 1 − e ln(λ₀/(λ₀−1))} / e^{m − 1 + e/(0.9λ₀ − 1)}`,
with `m = m_#(λ₀)`. -/
noncomputable def gConst (lam0 : ℝ) : ℝ :=
  mSharp lam0 *
      max (1 - Real.sqrt (Real.log (lam0 / (lam0 - 1))))
        (1 - Real.exp 1 * Real.log (lam0 / (lam0 - 1))) /
    Real.exp (mSharp lam0 - 1 + Real.exp 1 / (0.9 * lam0 - 1))

/-- **Upper end of the `h`-range**, arXiv:2209.13099v7, Theorem 4, p.30 (and (EC.136),
p.ec23): `g(λ₀) · 2 k c_ρ (n − 1) / (e n²)` for block size `k`, `n` users and constant `c`
(the theorem uses `c = c_ρ`). All quantities are real numbers. -/
noncomputable def hMax (lam0 : ℝ) (k : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  gConst lam0 * (2 * (k : ℝ) * c * ((n : ℝ) - 1) / (Real.exp 1 * (n : ℝ) ^ 2))

end BlockchainTFM


