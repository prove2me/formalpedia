-- Prove2me | Definitions.Def_PCLAssort_ip1Objective
-- name    : PCLAssort_ip1Objective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:18.517112+00:00
-- url     : https://prove2.me/theorems/3cae03fc-4528-4fa1-9fc5-d04bb2584a02
-- title:
--   Objective of the integer program IP$_1(z)$
-- statement:
--   For $z\in\mathbb R$ and $x\in\{0,1\}^n$, with $\bar r_i=r_i-z$, the objective of IP$_1(z)$ is
--
--   $$
--   \sum_{(i,j)\in M}\frac{\bar r_iv_i^{1/\gamma_{ij}}x_i+\bar r_jv_j^{1/\gamma_{ij}}x_j}{V_{ij}(x)^{1-\gamma_{ij}}}.
--   $$
--
--   **Formalization Note** For an empty nest the quotient $0/0$ is $0$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), IP$_1(z)$, p.791 (PDF p.7)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_nestWeight

namespace PCLAssort

/-- Objective of IP₁(z) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §3, p.791):
`∑_{(i,j)∈M} (r̄_i v_i^{1/γ_ij} x_i + r̄_j v_j^{1/γ_ij} x_j) / V_ij(x)^{1−γ_ij}`, at `x = 1_S`,
with `r̄_i = r_i − z`.

**Formalization Note.** For an empty nest the page's `0/0` is Lean's `0`. -/
noncomputable def ip1Objective {n : ℕ} (I : PCLInstance n) (z : ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
    ((I.r p.1 - z) * I.v p.1 ^ (1 / I.γ p.1 p.2) * (if p.1 ∈ S then 1 else 0) +
        (I.r p.2 - z) * I.v p.2 ^ (1 / I.γ p.1 p.2) * (if p.2 ∈ S then 1 else 0)) /
      nestWeight I S p.1 p.2 ^ (1 - I.γ p.1 p.2)

end PCLAssort


