-- Prove2me | Definitions.Def_PCLAssort_hz
-- name    : PCLAssort_hz
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:20:52.17741+00:00
-- url     : https://prove2.me/theorems/4a4f325b-12cd-4df9-85fc-73f6ad13ec4c
-- title:
--   The linearized objective $h_z(x)$
-- statement:
--   For $z\in\mathbb R$ and $x\in\{0,1\}^n$,
--
--   $$
--   h_z(x)=\sum_{(i,j)\in M}V_{ij}(x)^{\gamma_{ij}}\big(R_{ij}(x)-z\big).
--   $$
--
--   Since the denominator of $\pi$ is positive, $\pi(x)\ge z$ if and only if $h_z(x)\ge v_0z$; this linearizes the ratio objective.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), equation (3), p.790 (PDF p.6)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_nestWeight
import Definitions.Def_PCLAssort_nestRevenue

namespace PCLAssort

/-- The linearized objective of equation (3) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.790):
`h_z(x) = ∑_{(i,j)∈M} V_ij(x)^{γ_ij} (R_ij(x) − z)` for `x ∈ {0,1}^n`, here at `x = 1_S`. -/
noncomputable def hz {n : ℕ} (I : PCLInstance n) (z : ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
    nestWeight I S p.1 p.2 ^ I.γ p.1 p.2 * (nestRevenue I S p.1 p.2 - z)

end PCLAssort


