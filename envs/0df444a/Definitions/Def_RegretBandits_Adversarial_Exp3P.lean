-- Prove2me | Definitions.Def_RegretBandits_Adversarial_Exp3P
-- name    : RegretBandits_Adversarial_Exp3P
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:32:02.298331+00:00
-- url     : https://prove2.me/theorems/2ef0cd9f-170c-4d86-84cb-6556d47e3fdc
-- title:
--   Exp3.P forecaster (Fig. 3.1)
-- statement:
--   The **Exp3.P** forecaster of Bubeck and Cesa-Bianchi (Fig. 3.1, p. 29) runs against an adversary with gains $g_{i,t} \in [0,1]$ and has parameters $\eta \in \mathbb R_+$ and $\gamma, \beta \in [0,1]$.
--
--   Let $p_1$ be the uniform distribution on $\{1,\dots,K\}$. At each round $t = 1, 2, \dots$ the forecaster draws $I_t \sim p_t$, computes the biased gain estimates and their cumulative sums
--   $$
--   \tilde g_{i,t} = \frac{g_{i,t} \mathbb 1_{I_t = i} + \beta}{p_{i,t}}, \qquad \tilde G_{i,t} = \sum_{s=1}^t \tilde g_{i,s},
--   $$
--   and sets
--   $$
--   p_{i,t+1} = (1-\gamma) \frac{\exp(\eta \tilde G_{i,t})}{\sum_{k=1}^K \exp(\eta \tilde G_{k,t})} + \frac{\gamma}{K}.
--   $$
--   The definition gives the cumulative estimated gains $\tilde G_{i,t}$ along a sequence of actions and the resulting distribution $p_t$ at every round $t \ge 1$.
--
--   Exp3.P is the forecaster of Theorems 3.2 and 3.3. The bias $\beta$ makes $\tilde G_{i,t}$ an upper confidence bound on the true cumulative gain (Lemma 3.1), and the mixing with the uniform distribution keeps every $p_{i,t} \ge \gamma/K$.
--
--   **Formalization Note** The weights use $\exp(+\eta \tilde G)$ as in the algorithm box; the proof's display (3.16), which writes $\exp(-\eta \tilde G_{i,t-1})$, has a sign misprint. The formula is taken as printed for every real $\gamma$: for $\gamma \in [0,1]$ (the book's range) $p_t$ is a probability vector with positive entries; for $\gamma > 1$ it can have negative entries, and where that happens on a history of positive probability no run of the rule exists. At index $t = 0$, which is not a round, the definition returns $p_1$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 29, Section 3.2, Exp3.P (Fig. 3.1)

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol

namespace RegretBandits.Adversarial

/-- The Exp3.P mixture (Fig. 3.1, p. 29): from estimated cumulative gains `G`,
`(1 - γ) exp(η G_i) / ∑_k exp(η G_k) + γ / K`. -/
noncomputable def exp3PMix {K : ℕ} (γ η : ℝ) (G : Fin K → ℝ) (i : Fin K) : ℝ :=
  (1 - γ) * gibbs η G i + γ / K

/-- The estimated cumulative gain `G̃_{i,t} = ∑_{s=1}^t g̃_{i,s}` of Exp3.P (Fig. 3.1, p. 29) along
the action sequence `h` (`h s = I_s`), with
`g̃_{i,t+1} = (g_{i,t+1} 𝟙{I_{t+1} = i} + β) / p_{i,t+1}` and `p_{t+1} = exp3PMix γ η G̃_t`. -/
noncomputable def exp3PCumGain {K : ℕ} (β γ η : ℝ) (g : Adversary K) :
    ℕ → (ℕ → Fin K) → Fin K → ℝ
  | 0, _, _ => 0
  | t + 1, h, i =>
      exp3PCumGain β γ η g t h i +
        (g.val (t + 1) h i * (if h (t + 1) = i then 1 else 0) + β) /
          exp3PMix γ η (exp3PCumGain β γ η g t h) i

/-- The Exp3.P forecaster (Fig. 3.1, p. 29) with parameters `β, γ, η` against the adversary `g`
(gains): at round `t ≥ 1`,
`p_{i,t} = (1 - γ) exp(η G̃_{i,t-1}) / ∑_k exp(η G̃_{k,t-1}) + γ / K`; `p_1` is uniform since
`G̃_{·,0} = 0`. (At `t = 0`, which is not a round, the value equals `p_1`.) -/
noncomputable def exp3PProb {K : ℕ} (β γ η : ℝ) (g : Adversary K) (t : ℕ) (h : ℕ → Fin K) :
    Fin K → ℝ :=
  exp3PMix γ η (exp3PCumGain β γ η g (t - 1) h)

end RegretBandits.Adversarial


