-- Prove2me | Definitions.Def_ApproxOptRL_CPI_Algorithm
-- name    : ApproxOptRL_CPI_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:44:15.97328+00:00
-- url     : https://prove2.me/theorems/75e67ea7-bddc-45b5-8b46-99574fd1e8f8
-- title:
--   The conservative policy iteration algorithm as a run driven by a sequence of estimates
-- statement:
--   This file formalizes the conservative policy iteration algorithm of §5 of Kakade and Langford (ICML 2002), for a known accuracy $\varepsilon$, reward bound $R$ and discount $\gamma$, an $\varepsilon$-greedy policy chooser $G_\varepsilon$ and an initial policy $\pi_0$. Each loop of the algorithm is:
--
--   1. call $G_\varepsilon(\pi,\mu)$ to obtain some $\pi'$;
--   2. obtain an estimate $\hat{\mathbb A}$ of the policy advantage $\mathbb A_{\pi,\mu}(\pi')$;
--   3. if $\hat{\mathbb A} < \frac{2\varepsilon}{3}$, stop and return $\pi$;
--   4. otherwise replace $\pi$ by the conservative update (4.1) $(1-\alpha)\pi + \alpha\pi'$ with step size
--   $$\alpha = \frac{(1-\gamma)\big(\hat{\mathbb A} - \frac{\varepsilon}{3}\big)}{4R},$$
--   and return to step 1.
--
--   Given the sequence of estimates $\hat{\mathbb A}_0, \hat{\mathbb A}_1, \dots$ produced in loops $0, 1, \dots$, the definition computes the policy $\pi_j$ held at the start of loop $j$: $\pi_0$ is the initial policy, and $\pi_{j+1} = \pi_j$ if $\hat{\mathbb A}_j < \frac{2\varepsilon}3$ (the run has stopped and the policy is frozen), and otherwise $\pi_{j+1} = (1-\alpha_j)\pi_j + \alpha_j G_\varepsilon(\pi_j)$.
--
--   Theorem 4.4 of the paper is stated about this run.
--
--   **Formalization Note** The step size is clipped: $\alpha_j = \min\big(1, \frac{(1-\gamma)(\hat{\mathbb A}_j - \varepsilon/3)}{4R}\big)$, so that the update is a policy even for a wildly wrong estimate. Whenever the estimate is within $\varepsilon/3$ of the true policy advantage (which is at most $R$), the paper's step size is at most $(1-\gamma)/4<1$ and the clip does not bind. How the estimates are produced (step (2), by $\mu$-restarts) is not part of this definition; Theorem 4.4 assumes their accuracy guarantee.
-- source:
--   Kakade, Langford, Approximately Optimal Approximate Reinforcement Learning, ICML 2002, p. 6, §5 (the conservative policy iteration algorithm, steps (1)–(4))

import Mathlib
import Definitions.Def_ApproxOptRL_CPI_PolicyAdvantage

namespace ApproxOptRL.CPI

/-- The step size of step (4) of conservative policy iteration (ICML 2002, §5, p. 6):
`α = (1 - γ)(Â - ε/3) / (4R)` for the estimate `Â`, clipped at `1` so that the update (4.1)
is a policy even for a wildly wrong estimate. The clip never binds when `Â` is within `ε/3`
of the true policy advantage (then `α ≤ (1 - γ)/4`). -/
noncomputable def cpiStepSize (γ R ε x : ℝ) : ℝ :=
  min 1 ((1 - γ) * (x - ε / 3) / (4 * R))

/-- The policy held by conservative policy iteration (ICML 2002, §5, p. 6) at the start of
loop `j` (0-based), started from `π₀`, with the `ε`-greedy chooser `G` and the sequence of
policy-advantage estimates `e` (`e j` is the estimate `Â` computed in step (2) of loop `j`).
If `e j < 2ε/3` the algorithm stops in loop `j` and the policy is frozen from then on;
otherwise the policy is updated by (4.1) with `π' = G π` and step size `cpiStepSize`. -/
noncomputable def cpiPolicy {S A : Type} (γ R ε : ℝ) (G : (S → A → ℝ) → (S → A → ℝ))
    (π₀ : S → A → ℝ) (e : ℕ → ℝ) : ℕ → S → A → ℝ
  | 0 => π₀
  | j + 1 =>
      if e j < 2 * ε / 3 then cpiPolicy γ R ε G π₀ e j
      else mixPolicy (cpiStepSize γ R ε (e j)) (cpiPolicy γ R ε G π₀ e j)
        (G (cpiPolicy γ R ε G π₀ e j))

end ApproxOptRL.CPI


