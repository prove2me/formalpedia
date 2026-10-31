-- Prove2me | Definitions.Def_PCLAssort_xiShare
-- name    : PCLAssort_xiShare
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:19.918632+00:00
-- url     : https://prove2.me/theorems/5f377410-5dfa-4e08-aeaa-02994282c1f6
-- title:
--   Weight a nest puts on an edge into the dummy vertex
-- statement:
--   For a nest $(k,l)$ and $p\in\{k,l\}$, write $\bar r_p=r_p-z$. The weight that the pair $(k,l)$ puts on the edge $(p,n+1)$ is
--
--   $$
--   \frac{\bar r_p\,v_p^{1/\gamma_{kl}}}{\big(v_k^{1/\gamma_{kl}}+v_l^{1/\gamma_{kl}}\big)^{1-\gamma_{kl}}}.
--   $$
--
--   In the notation of (4), $\xi^+_{ij}$ is this quantity for $(k,l)=(i,j)$, $p=i$, and $\xi^-_{ji}$ for $(k,l)=(i,j)$, $p=j$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), equation (4), p.790 (PDF p.6)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance

namespace PCLAssort

/-- The weight that the ordered pair (nest) `(k, l)` puts on the edge `(p, n+1)`, for `p ∈ {k, l}`,
in the reduction of §3, equation (4) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.790):
`r̄_p v_p^{1/γ_kl} / (v_k^{1/γ_kl} + v_l^{1/γ_kl})^{1−γ_kl}`, with `r̄_p = r_p − z`.
So `ξ⁺_ij = xiShare I z i j i` and `ξ⁻_ji = xiShare I z i j j`. -/
noncomputable def xiShare {n : ℕ} (I : PCLInstance n) (z : ℝ) (k l p : Fin n) : ℝ :=
  (I.r p - z) * I.v p ^ (1 / I.γ k l) /
    (I.v k ^ (1 / I.γ k l) + I.v l ^ (1 / I.γ k l)) ^ (1 - I.γ k l)

end PCLAssort


