-- Prove2me | Definitions.Def_PCLAssort_optRevenue
-- name    : PCLAssort_optRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:52.900532+00:00
-- url     : https://prove2.me/theorems/1e383eb2-51f4-4768-a754-e2a2245eba34
-- title:
--   The optimal revenue $z^*$
-- statement:
--   The optimal value of the assortment optimization problem over a family $\mathcal F$ is
--
--   $$
--   z^*=\max_{x\in\mathcal F}\pi(x).
--   $$
--
--   **Formalization Note** A supremum over the finite family $\mathcal F$; it is attained when $\mathcal F$ is nonempty.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), equation (2), p.790 (PDF p.6)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_revenue

namespace PCLAssort

/-- The optimal expected revenue `z* = max_{x ∈ 𝓕} π(x)` of problem (2) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.790).

**Formalization Note.** A supremum over the finite set `𝓕` (a subset of `Finset (Fin n)`); when
`𝓕` is nonempty it is attained, so it is the paper's maximum. -/
noncomputable def optRevenue {n : ℕ} (I : PCLInstance n) (F : Set (Finset (Fin n))) : ℝ :=
  ⨆ S : F, revenue I S.1

end PCLAssort


