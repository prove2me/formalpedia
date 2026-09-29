-- Prove2me | Definitions.Def_ImprovedLinBandits_UCBDelta_IsUCBDeltaRun
-- name    : ImprovedLinBandits_UCBDelta_IsUCBDeltaRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:23:15.43517+00:00
-- url     : https://prove2.me/theorems/848be315-7c4d-4f29-bd28-5fd0159a12bc
-- title:
--   Runs of the UCB($\delta$) algorithm, eq. (4)
-- statement:
--   Fix $d$ arms with means $\mu_1, \dots, \mu_d$, noise $\eta_1, \eta_2, \dots$ and a confidence level $\delta$. A sequence of arms $I_1, I_2, \dots$ (a function of the outcome $\omega$) is a **run of UCB($\delta$)** if, for every outcome and every round $t \ge 1$, the arm $I_t$ is chosen from the statistics $N_{j,t-1}$, $\overline X_{j,t-1}$ of the rounds $1, \dots, t-1$ as follows.
--
--   1. If some arm $j$ has $N_{j,t-1} = 0$ (its width $c_{j,t-1}$ is $+\infty$ in the paper), then $I_t$ is one of the arms that have not been played yet.
--   2. Otherwise $I_t$ maximizes the upper confidence index
--   $$I_t \in \operatorname*{argmax}_{j}\ \overline X_{j,t-1} + c_{j,t-1},$$
--   where $c_{j,t-1} = c(N_{j,t-1})$ is the width of eq. (3).
--
--   Any tie-breaking is allowed. This is the action-selection rule (4) of the paper.
--
--   **Formalization Note** The paper writes (4) as $I_t = \operatorname{argmax}_i \overline X_{i,t} + c_{i,t}$ with the statistics at time $t$; since these already count round $t$, the rule is read with the statistics of rounds $1, \dots, t-1$. In Lean round $t+1$ uses the pull counts and empirical means after $t$ rounds. Clause 1 makes explicit the paper's convention $c = +\infty$ for an unplayed arm, which Lean's junk value $0$ would otherwise break. A run always exists: at each round the rule selects from a nonempty finite set of arms.
-- source:
--   Abbasi-Yadkori, Pál, Szepesvári, Improved Algorithms for Linear Stochastic Bandits, NIPS 2011, p. 7, §6 eq. (4)

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel

namespace ImprovedLinBandits.UCBDelta

/-- `I` is a run of UCB(δ) (Abbasi-Yadkori, Pál, Szepesvári, NIPS 2011, §6, eq. (4), p. 7) on the
`d`-armed bandit with means `μ` and noise `η`: for every outcome `ω` and every round `t + 1`, the
arm `I (t + 1) ω` is chosen from the statistics of rounds `1, …, t` as follows.
1. If some arm has not been played in rounds `1, …, t` (its width `c` is `+∞` in the paper), then
   `I (t + 1) ω` is such an unplayed arm.
2. Otherwise `I (t + 1) ω` maximizes the index `X̄_{j,t} + c_{j,t}` over all arms `j`.
Every tie-breaking rule is allowed. -/
def IsUCBDeltaRun {Ω : Type*} (d : ℕ) (δ : ℝ) (μ : Fin d → ℝ) (η : ℕ → Ω → ℝ)
    (I : ℕ → Ω → Fin d) : Prop :=
  ∀ (ω : Ω) (t : ℕ),
    ((∃ j : Fin d, pullCount I j t ω = 0) → pullCount I (I (t + 1) ω) t ω = 0) ∧
    ((∀ j : Fin d, pullCount I j t ω ≠ 0) → ∀ j : Fin d,
      empMean μ η I j t ω + confRadius d δ (pullCount I j t ω) ≤
        empMean μ η I (I (t + 1) ω) t ω + confRadius d δ (pullCount I (I (t + 1) ω) t ω))

end ImprovedLinBandits.UCBDelta


