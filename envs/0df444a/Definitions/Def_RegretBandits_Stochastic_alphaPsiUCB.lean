-- Prove2me | Definitions.Def_RegretBandits_Stochastic_alphaPsiUCB
-- name    : RegretBandits_Stochastic_alphaPsiUCB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:19:20.042721+00:00
-- url     : https://prove2.me/theorems/d083e79c-e5aa-4d03-99aa-dc2af311df12
-- title:
--   The $(\alpha,\psi)$-UCB strategy
-- statement:
--   Let $T_j(t)$ be the number of times arm $j$ was played in rounds $1,\dots,t$, and $\hat\mu_{j,s}$ the sample mean of the first $s$ rewards of arm $j$. The **$(\alpha,\psi)$-UCB** strategy with parameter $\alpha>0$ selects, at round $t$,
--   $$I_t\in\operatorname*{argmax}_{j=1,\dots,K}\left[\hat\mu_{j,T_j(t-1)}+(\psi^*)^{-1}\!\left(\frac{\alpha\ln t}{T_j(t-1)}\right)\right].$$
--   A sequence of arms $I_1,I_2,\dots$ (a function of the outcome $\omega$) is a run of $(\alpha,\psi)$-UCB if at every round:
--
--   1. if some arm has not been played yet, an unplayed arm is played (its index $\alpha\ln t/0$ is $+\infty$); so the first $K$ rounds play every arm once;
--   2. otherwise the played arm maximizes the index above.
--
--   Ties may be broken arbitrarily.
--
--   This is the algorithm whose pseudo-regret Theorem 2.1 bounds.
--
--   **Formalization Note.** The book leaves the index undefined while $T_j(t-1)=0$; the convention "unplayed arms first" is the standard one. In Lean the arm of round $t+1$ is chosen from the counts at $t$, with $\ln(t+1)$ in the index.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 10, Section 2.2 ((α, ψ)-UCB)

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_RegretBandits_Stochastic_model

namespace RegretBandits.Stochastic

open ImprovedLinBandits.UCBDelta

/-- The (α, ψ)-UCB index of arm `j` used to choose the arm of round `t + 1`
(Bubeck and Cesa-Bianchi, arXiv:1204.5721v2, p. 10):
`μ̂_{j, T_j(t)} + (ψ*)⁻¹(α ln(t + 1) / T_j(t))`, where `T_j(t) = pullCount I j t ω` is the number
of times arm `j` was played in rounds `1, …, t`. Only used when `T_j(t) ≥ 1`. -/
noncomputable def ucbIndex {Ω : Type*} {K : ℕ} (ψ : ℝ → ℝ) (α : ℝ) (X : Fin K → ℕ → Ω → ℝ)
    (I : ℕ → Ω → Fin K) (j : Fin K) (t : ℕ) (ω : Ω) : ℝ :=
  sampleMean X j (pullCount I j t ω) ω +
    lfInv ψ (α * Real.log ((t : ℝ) + 1) / (pullCount I j t ω : ℝ))

/-- `I` is a run of (α, ψ)-UCB (p. 10) on the reward stack `X`: for every outcome `ω` and every
round `t + 1`,
1. if some arm has not been played in rounds `1, …, t` (its index `α ln t / 0` is `+∞`), then
   `I (t + 1) ω` is such an unplayed arm; in particular rounds `1, …, K` play every arm once;
2. otherwise `I (t + 1) ω` maximizes the index `ucbIndex` over all arms.
Every tie-breaking rule is allowed. -/
def IsAlphaPsiUCBRun {Ω : Type*} {K : ℕ} (ψ : ℝ → ℝ) (α : ℝ) (X : Fin K → ℕ → Ω → ℝ)
    (I : ℕ → Ω → Fin K) : Prop :=
  ∀ (ω : Ω) (t : ℕ),
    ((∃ j : Fin K, pullCount I j t ω = 0) → pullCount I (I (t + 1) ω) t ω = 0) ∧
    ((∀ j : Fin K, pullCount I j t ω ≠ 0) → ∀ j : Fin K,
      ucbIndex ψ α X I j t ω ≤ ucbIndex ψ α X I (I (t + 1) ω) t ω)

end RegretBandits.Stochastic


