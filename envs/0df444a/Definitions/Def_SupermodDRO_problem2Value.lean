-- Prove2me | Definitions.Def_SupermodDRO_problem2Value
-- name    : SupermodDRO_problem2Value
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:12.850993+00:00
-- url     : https://prove2.me/theorems/425a848f-2ed0-45fb-8015-f63ab9f272d2
-- title:
--   Optimal value of Problem (2)
-- statement:
--   The two-stage distributionally robust problem is
--   $$
--   \min_{x\in\mathcal X}\Bigl\{a^\top x+\sup_{\mathbb P\in\mathcal F}\mathbb E_{\mathbb P}[g(x,\tilde z)]\Bigr\}. \tag{2}
--   $$
--   Its optimal value is the infimum over $x\in\mathcal X$; $x\in\mathcal X$ is optimal when it attains this value.
--
--   **Formalization Note** The minimum is the infimum in $[-\infty,+\infty]$; attainment is not assumed.
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), §2.1, (2), p.6

import Mathlib
import Definitions.Def_SupermodDRO_worstCaseCost

open Matrix

namespace SupermodDRO

/-- **The optimal value of Problem (2).** Long, Qi & Zhang, *Supermodularity in Two-Stage
Distributionally Robust Optimization*, author manuscript (June 2022), §2.1, (2), p.6:
"min_{x∈𝒳} {a⊤x + sup_{ℙ∈𝓕} E_ℙ[g(x, z̃)]}".

**Formalization Note** The minimum is read as the infimum in `EReal` (attainment is not assumed);
`x ∈ 𝒳` is optimal for (2) when `a⊤x + sup_{ℙ∈𝓕} E_ℙ[g(x, z̃)]` equals this value. -/
noncomputable def problem2Value {l m r n K s : ℕ} (D : Data l m r n K s) : EReal :=
  ⨅ x ∈ D.X, ((D.a ⬝ᵥ x : ℝ) : EReal) + worstCaseCost D x

end SupermodDRO


