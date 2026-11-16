-- Prove2me | Definitions.Def_StableVotingDistortion_Supplement_lambdaK
-- name    : StableVotingDistortion_Supplement_lambdaK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:54:37.317208+00:00
-- url     : https://prove2.me/theorems/795ee1f1-439b-45fd-b592-6f72f1d4655b
-- title:
--   The constant $\lambda_k$ of Theorems 6 and 8
-- statement:
--   For an integer $k\ge2$,
--   $$
--   \lambda_k=\frac{1+(k-1)(k+1)^{-1/(k-1)}}{k},
--   $$
--   and $\lambda_1=1$. For example $\lambda_2=\lambda_3=2/3$, so $1+2\lambda_2=1+2\lambda_3=7/3$.
--
--   The quantity $1+2\lambda_k$ is the exact worst-case distortion of stable $k$-lotteries (Theorems 6 and 8).
--
--   **Formalization Note** The power is the real power of the positive base $k+1$. The case $k=1$, where the exponent is undefined, returns the separately printed value $1$; the value at $k=0$ is never used.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 6, p.14; Theorem 8, p.38

import Mathlib

set_option autoImplicit false

namespace StableVotingDistortion.Supplement

/-- The constant `λ_k = (1 + (k − 1)(k + 1)^{−1/(k−1)}) / k` for an integer `k ≥ 2`, and `λ_1 = 1`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 6, p.14: "λk = (1 + (k −1)(k + 1)^{−1/(k−1)}) / k
and λ1 = 1"; Theorem 8, p.38 (the same formula for every integer k > 1).

**Formalization Note.** The power is the real power `Real.rpow` of the positive base `k + 1`, and the whole
numerator is divided by `k` (so `λ_2 = λ_3 = 2/3`). The case `k = 1`, where the exponent `−1/(k−1)` is undefined,
is the separately printed value `λ_1 = 1`. The value at `k = 0` is not used. -/
noncomputable def lambdaK (k : ℕ) : ℝ :=
  if k = 1 then 1
  else (1 + ((k : ℝ) - 1) * ((k : ℝ) + 1) ^ (-(1 / ((k : ℝ) - 1)))) / k

end StableVotingDistortion.Supplement


