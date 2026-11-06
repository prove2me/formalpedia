-- Prove2me | Definitions.Def_AltRegret_potentialObjective
-- name    : AltRegret_potentialObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:07:17.198464+00:00
-- url     : https://prove2.me/theorems/17e7ab8e-f7e5-4e5b-821c-964a897f1b64
-- title:
--   The function maximized in the potential (2)
-- statement:
--   For the algorithm with parameters $(\eta,\beta)$, a round $t\ge1$ and $\theta\in\mathbb R$, set
--   $$
--   G_t(\theta)=\log\sum_{i=1}^{d}\exp\!\big[\eta R_{t-1,i}-\beta(c_{t-1,i}-\theta)^2\big],
--   $$
--   where $R_{t-1}$ is the alternating regret vector. The potential $\Phi_t$ of equation (2) is the maximum of $G_t$ over $\theta\in\mathbb R$.
--
--   **Formalization Note** $\log$ is the natural logarithm; $c_0=\mathbf 0$.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, §2.2, p.7, Eq. (2)

import Mathlib
import Definitions.Def_AltRegret_regretVector

namespace AltRegret

/-- **The function maximized in the potential (2).** Tao–Zheng, arXiv:2608.24731, §2.2, p.7,
Eq. (2): `Φ_t := max_{θ∈ℝ} log(∑_{i=1}^d exp[ηR_{t−1,i} − β(c_{t−1,i} − θ)²])`.

`potentialObjective η β c t θ = log ∑_i exp(η R_{t−1,i} − β (c_{t−1,i} − θ)²)`, with `R` the
alternating regret vector of the algorithm with parameters `(η, β)`.

**Formalization Note.** Read at rounds `t ≥ 1`; natural logarithm; `c₀ = 0` via `lossAt`. -/
noncomputable def potentialObjective {d : ℕ} (η β : ℝ) (c : ℕ → Fin d → ℝ) (t : ℕ) (θ : ℝ) :
    ℝ :=
  Real.log (∑ i, Real.exp (η * regretVector η β c (t - 1) i - β * (lossAt c (t - 1) i - θ) ^ 2))

end AltRegret


