-- Prove2me | Definitions.Def_PCLAssort_revenue
-- name    : PCLAssort_revenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:20:49.710005+00:00
-- url     : https://prove2.me/theorems/72ca181f-c346-47c0-a63e-45800c0b1b05
-- title:
--   Expected revenue $\pi(x)$ under the PCL model
-- statement:
--   The expected revenue of an assortment $x\in\{0,1\}^n$ under the PCL model is
--
--   $$
--   \pi(x)=\frac{\sum_{(i,j)\in M}V_{ij}(x)^{\gamma_{ij}}R_{ij}(x)}{v_0+\sum_{(k,l)\in M}V_{kl}(x)^{\gamma_{kl}}}.
--   $$
--
--   The assortment optimization problem maximizes $\pi$ over a family $\mathcal F$ of feasible assortments.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), equation (1), p.790 (PDF p.6)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_nestWeight
import Definitions.Def_PCLAssort_nestRevenue

namespace PCLAssort

/-- Expected revenue of an assortment under the PCL model, equation (1) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.790):
`π(x) = ∑_{(i,j)∈M} V_ij(x)^{γ_ij} R_ij(x) / (v_0 + ∑_{(k,l)∈M} V_kl(x)^{γ_kl})`, where
`M = {(i, j) | i ≠ j}` is the set of nests.

**Formalization Note.** `x = 1_S`; `M` is `Finset.univ.offDiag`. -/
noncomputable def revenue {n : ℕ} (I : PCLInstance n) (S : Finset (Fin n)) : ℝ :=
  (∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
      nestWeight I S p.1 p.2 ^ I.γ p.1 p.2 * nestRevenue I S p.1 p.2) /
    (I.v0 + ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, nestWeight I S p.1 p.2 ^ I.γ p.1 p.2)

end PCLAssort


