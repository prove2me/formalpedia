-- Prove2me | Definitions.Def_BayesBAI_dropOne
-- name    : BayesBAI_dropOne
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:55.618989+00:00
-- url     : https://prove2.me/theorems/f72797bb-935a-41fd-a3f7-1c48bb21409d
-- title:
--   The vector $\mu_{\setminus i}$
-- statement:
--   $\mu_{\setminus i}$ is the set of the $K-1$ parameters other than $\mu_i$. The law of $\mu_{\setminus i}$ under $H$ is $H_{\setminus i}$.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, §1.1, p.2

import Mathlib

namespace BayesBAI

/-- `μ_\i`, the `K - 1` parameters other than `μ_i`, Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3,
§1.1, p.2. This map is `Measurable`, so `H.map (dropOne i)` is the law `H_\i` of `μ_\i` under `H`. -/
def dropOne {K : ℕ} (i : Fin K) (μ : Fin K → ℝ) : {j : Fin K // j ≠ i} → ℝ :=
  fun j => μ j

end BayesBAI


