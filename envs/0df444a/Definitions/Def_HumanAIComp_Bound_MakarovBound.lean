-- Prove2me | Definitions.Def_HumanAIComp_Bound_MakarovBound
-- name    : HumanAIComp_Bound_MakarovBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:36:55.510856+00:00
-- url     : https://prove2.me/theorems/59693466-d3a6-4944-a816-1a3a93a3fdfb
-- title:
--   Theorem 1, p. 17 — the bound ε = sup_t (F_a(t) − F_b(t + δ)) for two laws on ℝ
-- statement:
--   Let $\mu_a$ and $\mu_b$ be probability measures on $\mathbb R$ with right-continuous cumulative distribution functions $F_a(t)=\mu_a((-\infty,t])$ and $F_b(t)=\mu_b((-\infty,t])$, and let $\delta\in\mathbb R$ be a threshold. The quantity
--   $$
--   \varepsilon(\delta)\;=\;\sup_{t\in\mathbb R}\bigl(F_a(t)-F_b(t+\delta)\bigr)
--   $$
--   is the right-hand side of Theorem 1 of Baek, Fu, Ma and Peng: when $a$ and $b$ are random variables with these laws, it is the sharp distribution-free lower bound on $\mathbb P[b-a>\delta]$ over all joint laws of $(a,b)$.
--
--   Every term $F_a(t)-F_b(t+\delta)$ lies in $[-1,1]$, so the supremum is a finite real number. The definition is shared by the goal theorem and every milestone of the mission.
--
--   **Formalization Note** The supremum is Lean's real `iSup` over $t\in\mathbb R$. For probability measures the family is bounded above by $1$, so this is the true supremum and no default value is involved.
-- source:
--   Baek, Fu, Ma, Peng, AI Agents for Inventory Control: Human-LLM-OR Complementarity, arXiv:2602.12631v2, p. 17, Theorem 1; p. 46, proof of Theorem 1 (definition of ε)

import Mathlib

namespace HumanAIComp.Bound

open MeasureTheory ProbabilityTheory

/-- The bound of Theorem 1 (Baek–Fu–Ma–Peng, arXiv:2602.12631v2, p. 17):
`ε(δ) = sup_{t ∈ ℝ} (F_a(t) − F_b(t + δ))`, where `F_a = cdf μa` and `F_b = cdf μb` are the
right-continuous CDFs `F(t) = μ((−∞, t])` of two laws on `ℝ`. For probability measures every term
of the family lies in `[−1, 1]`, so the family is bounded and the real `iSup` is the true
supremum (no junk value is involved). -/
noncomputable def makarovBound (δ : ℝ) (μa μb : Measure ℝ) : ℝ :=
  ⨆ t : ℝ, (cdf μa t - cdf μb (t + δ))

end HumanAIComp.Bound


