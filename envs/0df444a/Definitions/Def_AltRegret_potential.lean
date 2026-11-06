-- Prove2me | Definitions.Def_AltRegret_potential
-- name    : AltRegret_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:08:36.486215+00:00
-- url     : https://prove2.me/theorems/2e7d69d5-6ea7-443e-8d75-6785912d9421
-- title:
--   The potential $\Phi_t$ of (2)
-- statement:
--   The **potential** of the algorithm with parameters $(\eta,\beta)$ at round $t\ge1$ is
--   $$
--   \Phi_t=\max_{\theta\in\mathbb R}\ \log\sum_{i=1}^{d}\exp\!\big[\eta R_{t-1,i}-\beta(c_{t-1,i}-\theta)^2\big].
--   $$
--   The analysis shows that $\Phi_1=\log d$ and that $\Phi_t$ never increases (Theorem 5); together with $\Phi_{T+1}\ge\eta R_{T,i}$ this bounds the alternating regret.
--
--   **Formalization Note** The maximum is written as the supremum over $\theta\in\mathbb R$. For $\beta\ge0$ the values are bounded above by $\log\sum_i\exp(\eta R_{t-1,i})$, so the supremum is a genuine least upper bound and not a default value; that it is attained, at the algorithm's $\theta_t$, is the milestone `AltRegret.eq_2`. No statement uses $\beta<0$.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, §2.2, p.7, Eq. (2)

import Mathlib
import Definitions.Def_AltRegret_potentialObjective

namespace AltRegret

/-- **The potential `Φ_t`.** Tao–Zheng, arXiv:2608.24731, §2.2, p.7, Eq. (2): "The potential
function is `Φ_t := max_{θ∈ℝ} log(∑_{i=1}^d exp[ηR_{t−1,i} − β(c_{t−1,i} − θ)²])`".

`potential η β c t = ⨆ θ ∈ ℝ, potentialObjective η β c t θ`.

**Formalization Note.** The maximum is written as a supremum over `ℝ`. For `β ≥ 0` the values
are bounded above by `log ∑_i exp(ηR_{t−1,i})` (for `d ≥ 1`; for `d = 0` they are all `0`), so the
supremum is a genuine least upper bound and not Lean's default value; that it is attained, at the
algorithm's `θ_t`, is the first clause of `AltRegret.eq_2`. For `β < 0` the set is unbounded and
the value is meaningless; no statement uses that range. -/
noncomputable def potential {d : ℕ} (η β : ℝ) (c : ℕ → Fin d → ℝ) (t : ℕ) : ℝ :=
  ⨆ θ : ℝ, potentialObjective η β c t θ

end AltRegret


