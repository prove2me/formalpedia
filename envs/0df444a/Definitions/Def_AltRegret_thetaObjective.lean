-- Prove2me | Definitions.Def_AltRegret_thetaObjective
-- name    : AltRegret_thetaObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:53.045089+00:00
-- url     : https://prove2.me/theorems/bc311203-c686-4d18-a5ce-571c0f19a4f2
-- title:
--   The objective $F_t(\theta)$ of line 3 of Algorithm 1
-- statement:
--   Fix parameters $\eta,\beta\in\mathbb R$, a loss sequence $c$ (with $c_0=\mathbf 0$) and a round $t\ge1$. Line 3 of Algorithm 1 (alternation-aware Hedge) maximizes over $\theta\in\mathbb R$ the function
--   $$
--   F_t(\theta)=\log\sum_{i=1}^{d}\exp\!\big[-\eta L_{t-1,i}-\beta(c_{t-1,i}-\theta)^2\big],
--   $$
--   where $L_{t-1}$ is the effective cumulative loss. The proof of Lemma 1 calls this function $F(\theta)$.
--
--   **Formalization Note** The algorithm is parametrized by $(\eta,\beta)$ because Lemma 1 and Theorem 5 vary these parameters; Algorithm 1 as printed is $\eta=1/8$, $\beta=1/32$. $\log$ is the natural logarithm.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, §2.1, p.6, Algorithm 1, line 3; proof of Lemma 1, p.7

import Mathlib
import Definitions.Def_AltRegret_effCumLoss

namespace AltRegret

/-- **The objective `F_t(θ)` of line 3 of Algorithm 1.** Tao–Zheng, arXiv:2608.24731, §2.1, p.6,
Algorithm 1 (alternation-aware Hedge), line 3: "Compute
`θ_t = argmax_{θ∈ℝ} log ∑_{i=1}^d exp[−ηL_{t−1,i} − β(c_{t−1,i} − θ)²]`"; the proof of Lemma 1
(p.7) names this function `F(θ)`.

`thetaObjective η β c t θ = log ∑_i exp(−η L_{t−1,i} − β (c_{t−1,i} − θ)²)`.

**Formalization Note.** Algorithm 1 fixes `η = 1/8`, `β = 1/32`; Lemma 1 and Theorem 5 vary
them, so the algorithm is parametrized by `(η, β)`. It is read at rounds `t ≥ 1`; `Real.log` is
the natural logarithm. -/
noncomputable def thetaObjective {d : ℕ} (η β : ℝ) (c : ℕ → Fin d → ℝ) (t : ℕ) (θ : ℝ) : ℝ :=
  Real.log (∑ i, Real.exp (-η * effCumLoss c (t - 1) i - β * (lossAt c (t - 1) i - θ) ^ 2))

end AltRegret


