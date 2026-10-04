-- Prove2me | Definitions.Def_RegretBandits_Adversarial_Exp3
-- name    : RegretBandits_Adversarial_Exp3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:32:03.120592+00:00
-- url     : https://prove2.me/theorems/326c16b3-c75b-4ac1-801d-261d8af526ff
-- title:
--   Exp3 forecaster (box, p. 23)
-- statement:
--   The **Exp3** forecaster (Exponential weights for Exploration and Exploitation) of Bubeck and Cesa-Bianchi (box, p. 23) runs against an adversary with losses $\ell_{i,t} \in [0,1]$ and is parametrized by a non-increasing sequence of learning rates $(\eta_t)_{t \in \mathbb N}$.
--
--   Let $p_1$ be the uniform distribution on $\{1,\dots,K\}$. At each round $t = 1, 2, \dots$ the forecaster draws $I_t \sim p_t$, computes the importance-weighted loss estimates and their cumulative sums
--   $$
--   \tilde\ell_{i,t} = \frac{\ell_{i,t}}{p_{i,t}} \mathbb 1_{I_t = i}, \qquad \tilde L_{i,t} = \tilde L_{i,t-1} + \tilde\ell_{i,t}, \qquad \tilde L_{i,0} = 0,
--   $$
--   and sets
--   $$
--   p_{i,t+1} = \frac{\exp(-\eta_t \tilde L_{i,t})}{\sum_{k=1}^K \exp(-\eta_t \tilde L_{k,t})}.
--   $$
--   The definition gives the cumulative estimated losses $\tilde L_{i,t}$ along a sequence of actions and the resulting distribution $p_t$ at every round $t \ge 1$.
--
--   Exp3 is the forecaster of Theorem 3.1.
--
--   **Formalization Note** The book's box writes "$\tilde L_{i,t} = \tilde L_{i,t-1} + \tilde\ell_{i,s}$"; the index $s$ is a misprint for $t$, and the definition uses $\tilde\ell_{i,t}$. The update follows the box: the distribution of round $t+1$ uses $\eta_t$. The value $\eta_0$ is never effective, because it multiplies $\tilde L_{\cdot,0} = 0$. At index $t = 0$, which is not a round, the definition returns the uniform vector.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 23, Section 3.1, Exp3 (box)

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol

namespace RegretBandits.Adversarial

/-- The estimated cumulative loss `L̃_{i,t}` of Exp3 (box, p. 23) after rounds `1, …, t`, along the
action sequence `h` (`h s = I_s`), for the learning rates `η : ℕ → ℝ` and the adversary `ℓ`
(losses). `L̃_{i,0} = 0` and
`L̃_{i,t+1} = L̃_{i,t} + ℓ̃_{i,t+1}`, `ℓ̃_{i,t+1} = ℓ_{i,t+1} 𝟙{I_{t+1} = i} / p_{i,t+1}`,
where `p_{t+1} = gibbs (-η_t) L̃_t` is the Exp3 distribution of round `t + 1`. -/
noncomputable def exp3CumLoss {K : ℕ} (η : ℕ → ℝ) (ℓ : Adversary K) :
    ℕ → (ℕ → Fin K) → Fin K → ℝ
  | 0, _, _ => 0
  | t + 1, h, i =>
      exp3CumLoss η ℓ t h i +
        ℓ.val (t + 1) h i * (if h (t + 1) = i then 1 else 0) /
          gibbs (-η t) (exp3CumLoss η ℓ t h) i

/-- The Exp3 forecaster (box, p. 23) with the non-increasing learning rates `(η_t)`: at round
`t ≥ 1`, `p_{i,t} = exp(-η_{t-1} L̃_{i,t-1}) / ∑_k exp(-η_{t-1} L̃_{k,t-1})`; `p_1` is uniform since
`L̃_{·,0} = 0`. (At `t = 0`, which is not a round, the value is the uniform vector.) -/
noncomputable def exp3Prob {K : ℕ} (η : ℕ → ℝ) (ℓ : Adversary K) (t : ℕ) (h : ℕ → Fin K) :
    Fin K → ℝ :=
  gibbs (-η (t - 1)) (exp3CumLoss η ℓ (t - 1) h)

end RegretBandits.Adversarial


