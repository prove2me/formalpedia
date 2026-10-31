-- Prove2me | Definitions.Def_PCLAssort_ip1Value
-- name    : PCLAssort_ip1Value
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:20:52.431366+00:00
-- url     : https://prove2.me/theorems/0a7f75c7-37c1-4652-b990-9bb326b2bc5d
-- title:
--   Optimal value of IP$_1(z)$
-- statement:
--   The optimal value of IP$_1(z)$ is the maximum of its objective over $x\in\{0,1\}^n$ with $x\in\mathcal F$.
--
--   **Formalization Note** A supremum over the finite family $\mathcal F$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), IP$_1(z)$, p.791 (PDF p.7)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_ip1Objective

namespace PCLAssort

/-- Optimal value of IP₁(z) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §3, p.791): the maximum of its objective over `x ∈ {0,1}^n`,
`x ∈ 𝓕`.

**Formalization Note.** A supremum over the finite family `𝓕`, attained when `𝓕` is nonempty. -/
noncomputable def ip1Value {n : ℕ} (I : PCLInstance n) (F : Set (Finset (Fin n))) (z : ℝ) : ℝ :=
  ⨆ S : F, ip1Objective I z S.1

end PCLAssort


