-- Prove2me | Definitions.Def_AltRegret_theta
-- name    : AltRegret_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:02:31.156195+00:00
-- url     : https://prove2.me/theorems/03d4df9e-a30b-43d5-85ba-23b87f1bb42c
-- title:
--   The centering scalar $\theta_t=\arg\max_\theta F_t(\theta)$ of Algorithm 1
-- statement:
--   In round $t\ge1$, Algorithm 1 computes
--   $$
--   \theta_t=\arg\max_{\theta\in\mathbb R}\ \log\sum_{i=1}^{d}\exp\!\big[-\eta L_{t-1,i}-\beta(c_{t-1,i}-\theta)^2\big]=\arg\max_{\theta\in\mathbb R}F_t(\theta).
--   $$
--   This definition returns a maximizer of $F_t$ whenever one exists.
--
--   Lemma 1 shows that under the paper's assumptions ($0<\beta<1/2$, $c_{t-1}\in[-1,1]^d$) the maximizer exists and is unique, so the value is the paper's $\theta_t$.
--
--   **Formalization Note** When $F_t$ has no maximizer the definition returns $0$; this case does not arise under the paper's assumptions, and Lemma 1 (`AltRegret.lemma_1`) states that the value chosen is the unique maximizer.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, §2.1, p.6, Algorithm 1, line 3

import Mathlib
import Definitions.Def_AltRegret_thetaObjective

namespace AltRegret

open Classical in
/-- **The centering scalar `θ_t` of Algorithm 1.** Tao–Zheng, arXiv:2608.24731, §2.1, p.6,
Algorithm 1, line 3: "Compute `θ_t = argmax_{θ∈ℝ} log ∑_{i=1}^d exp[−ηL_{t−1,i} − β(c_{t−1,i} − θ)²]`".

`theta η β c t` is a maximizer of `thetaObjective η β c t` when one exists.

**Formalization Note.** When no maximizer exists the value `0` is returned; this case never
arises under the paper's assumptions: Lemma 1 (`AltRegret.lemma_1`) asserts that for
`0 < β < 1/2` and `c_{t−1} ∈ [−1,1]^d` the maximizer exists, is unique, and is the value chosen
here. The algorithm is parametrized by `(η, β)`; Algorithm 1 is `η = 1/8`, `β = 1/32`. -/
noncomputable def theta {d : ℕ} (η β : ℝ) (c : ℕ → Fin d → ℝ) (t : ℕ) : ℝ :=
  if h : ∃ θ : ℝ, ∀ θ' : ℝ, thetaObjective η β c t θ' ≤ thetaObjective η β c t θ then
    Classical.choose h
  else 0

end AltRegret


