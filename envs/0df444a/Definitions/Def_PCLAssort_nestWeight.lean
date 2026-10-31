-- Prove2me | Definitions.Def_PCLAssort_nestWeight
-- name    : PCLAssort_nestWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:22.511291+00:00
-- url     : https://prove2.me/theorems/5b071e76-d46f-4fe8-9d6a-8e714ec29dbd
-- title:
--   The nest quantity $V_{ij}(x)$
-- statement:
--   For an assortment $x\in\{0,1\}^n$ and a nest $(i,j)$,
--
--   $$
--   V_{ij}(x)=v_i^{1/\gamma_{ij}}x_i+v_j^{1/\gamma_{ij}}x_j,
--   $$
--
--   and the preference weight of the nest is $V_{ij}(x)^{\gamma_{ij}}$.
--
--   **Formalization Note** The assortment is a finite set $S\subseteq[n]$ with indicator $x=\mathbf 1_S$; real powers are `Real.rpow`.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §2, p.789 (PDF p.5)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance

namespace PCLAssort

/-- The quantity `V_ij(x) = v_i^{1/γ_ij} x_i + v_j^{1/γ_ij} x_j` of the PCL model (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §2, p.789),
at the indicator vector `x = 1_S` of an assortment `S ⊆ [n]`; the preference weight of the nest
`(i, j)` is `V_ij(x)^{γ_ij}`.

**Formalization Note.** Assortments are `Finset (Fin n)` and `x_i = 1` iff `i ∈ S`. Real powers are
`Real.rpow`. -/
noncomputable def nestWeight {n : ℕ} (I : PCLInstance n) (S : Finset (Fin n)) (i j : Fin n) : ℝ :=
  I.v i ^ (1 / I.γ i j) * (if i ∈ S then 1 else 0) + I.v j ^ (1 / I.γ i j) * (if j ∈ S then 1 else 0)

end PCLAssort


