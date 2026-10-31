-- Prove2me | Definitions.Def_PCLAssort_nestRevenue
-- name    : PCLAssort_nestRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:49.494907+00:00
-- url     : https://prove2.me/theorems/819ad2f0-66c6-4408-ac22-2ad788cec91b
-- title:
--   Expected revenue $R_{ij}(x)$ of a chosen nest
-- statement:
--   Given that the customer chose nest $(i,j)$, the expected revenue is
--
--   $$
--   R_{ij}(x)=\frac{r_iv_i^{1/\gamma_{ij}}x_i+r_jv_j^{1/\gamma_{ij}}x_j}{V_{ij}(x)}.
--   $$
--
--   **Formalization Note** For an empty nest ($x_i=x_j=0$) the quotient $0/0$ is $0$; such a nest has preference weight $0$ and contributes nothing.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §2, p.789 (PDF p.5)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_nestWeight

namespace PCLAssort

/-- Expected revenue from nest `(i, j)` given that the customer chose it (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §2, p.789):
`R_ij(x) = (r_i v_i^{1/γ_ij} x_i + r_j v_j^{1/γ_ij} x_j) / V_ij(x)`, at `x = 1_S`.

**Formalization Note.** For an empty nest (`x_i = x_j = 0`) the page's `0/0` is Lean's `0`; the
nest then has preference weight `V_ij(x)^{γ_ij} = 0` (as `γ_ij > 0`) and contributes nothing. -/
noncomputable def nestRevenue {n : ℕ} (I : PCLInstance n) (S : Finset (Fin n)) (i j : Fin n) : ℝ :=
  (I.r i * I.v i ^ (1 / I.γ i j) * (if i ∈ S then 1 else 0) +
      I.r j * I.v j ^ (1 / I.γ i j) * (if j ∈ S then 1 else 0)) / nestWeight I S i j

end PCLAssort


