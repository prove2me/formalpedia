-- Prove2me | Definitions.Def_BayesBAI_dropTwo
-- name    : BayesBAI_dropTwo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:54.516415+00:00
-- url     : https://prove2.me/theorems/7f0c8189-a6a2-42f0-b7a1-bc5bd9952c1e
-- title:
--   The vector $\mu_{\setminus ij}$
-- statement:
--   $\mu_{\setminus ij}$ is the set of the $K-2$ parameters other than $\mu_i,\mu_j$. The law of $\mu_{\setminus ij}$ under $H$ is $H_{\setminus ij}$; for $K=2$ it is a point mass.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, §1.1, p.2

import Mathlib

namespace BayesBAI

/-- `μ_\ij`, the `K - 2` parameters other than `μ_i, μ_j`, Komiyama, Ariu, Kato, Qin,
arXiv:2111.09885v3, §1.1, p.2. This map is `Measurable`, so `H.map (dropTwo i j)` is the law `H_\ij` of
`μ_\ij` under `H`. For `K = 2` the index type is empty and that law is a point mass. -/
def dropTwo {K : ℕ} (i j : Fin K) (μ : Fin K → ℝ) : {k : Fin K // k ≠ i ∧ k ≠ j} → ℝ :=
  fun k => μ k

end BayesBAI


