-- Prove2me | Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
-- name    : ImprovedLinBandits_UCBDelta_armModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:22:37.647645+00:00
-- url     : https://prove2.me/theorems/209addc6-623b-478b-8560-50bb796325f7
-- title:
--   The $d$-armed bandit of §6: best mean, gaps, pull counts, empirical means, pseudo-regret and the widths $c_{i,t}$
-- statement:
--   Consider a $d$-armed bandit with arms $i \in \{1, \dots, d\}$ and expected rewards $\mu_1, \dots, \mu_d \in \mathbb R$. In round $t$ the learner plays an arm $I_t$ and receives the reward $\mu_{I_t} + \eta_t$, where $\eta_t$ is a noise term. This file defines the quantities of Section 6 of the paper.
--
--   1. The **best mean** $\mu_* = \max_{1 \le i \le d} \mu_i$ and the **gap** of arm $i$, $\Delta_i = \mu_* - \mu_i \ge 0$.
--   2. The **pull count** $N_{i,t}$: the number of rounds $s \in \{1, \dots, t\}$ with $I_s = i$. In particular $N_{i,0} = 0$.
--   3. The **empirical mean** $\overline X_{i,t}$: the average of the rewards $\mu_{I_s} + \eta_s$ over the rounds $s \in \{1,\dots,t\}$ with $I_s = i$,
--   $$\overline X_{i,t} = \frac{1}{N_{i,t}} \sum_{s \le t,\ I_s = i} \left(\mu_i + \eta_s\right).$$
--   4. The **pseudo-regret** after $n$ rounds, $R_n = \sum_{t=1}^n \left(\mu_* - \mu_{I_t}\right)$, which is the pseudo-regret of Section 1.2 when the decision set is the standard basis of $\mathbb R^d$ and $\theta_* = \mu$.
--   5. The **confidence width** of eq. (3), as a function of the pull count $N = N_{i,t}$ and the confidence level $\delta$:
--   $$c(N) = \sqrt{\frac{1 + N}{N^2}\left(1 + 2\log\left(\frac{d\,(1 + N)^{1/2}}{\delta}\right)\right)} .$$
--
--   These are the objects in terms of which Lemma 6 (confidence intervals), the UCB($\delta$) rule (4) and Theorem 7 (constant regret) are stated.
--
--   **Formalization Note** The maximum $\mu_*$ is written as a supremum over the finite type of arms, which is the maximum when $d > 0$; every theorem using it assumes $d > 0$. Rounds are indexed $s + 1$ for $s \in \{0, \dots, t-1\}$, so values at index $0$ are never used. When $N_{i,t} = 0$ the paper's average is undefined and its width is $+\infty$; Lean's division by zero makes both the empirical mean and the width equal to $0$ there, so every statement using them treats $N = 0$ separately. The logarithm is the natural logarithm.
-- source:
--   Abbasi-Yadkori, Pál, Szepesvári, Improved Algorithms for Linear Stochastic Bandits, NIPS 2011, p. 7, §6 (definitions of $\mu_i$, $\mu_*$, $\Delta_i$, $N_{i,t}$, $\overline X_{i,t}$), Lemma 6 eq. (3); pp. 2–3, §1.2 (pseudo-regret)

import Mathlib

namespace ImprovedLinBandits.UCBDelta

/-- `μ_* = max_{1 ≤ i ≤ d} μ_i`, the expected reward of the best arm (Abbasi-Yadkori, Pál,
Szepesvári, NIPS 2011, §6, p. 7). Written as `⨆ i, μ i`, which is the maximum over the finite
type `Fin d` when `0 < d`; every theorem using it assumes `0 < d` (at `d = 0` the value is the
junk `0`). -/
noncomputable def bestMean {d : ℕ} (μ : Fin d → ℝ) : ℝ :=
  ⨆ i, μ i

/-- `Δ_i = μ_* - μ_i`, the gap of arm `i` with respect to the best arm (§6, p. 7). -/
noncomputable def gap {d : ℕ} (μ : Fin d → ℝ) (i : Fin d) : ℝ :=
  bestMean μ - μ i

/-- `N_{i,t}`, the number of rounds among `1, …, t` in which arm `i` was played. Round `s + 1`
plays arm `I (s + 1) ω`; `N_{i,0} = 0`. -/
def pullCount {Ω : Type*} {d : ℕ} (I : ℕ → Ω → Fin d) (i : Fin d) (t : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range t).filter (fun s => I (s + 1) ω = i)).card

/-- `X̄_{i,t}`, the average of the rewards `μ_{I_s} + η_s` received from arm `i` in the rounds
`s ∈ {1, …, t}` with `I_s = i`. When `N_{i,t} = 0` the paper's average is undefined and this
definition returns the junk value `0` (division by zero); every statement using it excludes that
case. -/
noncomputable def empMean {Ω : Type*} {d : ℕ} (μ : Fin d → ℝ) (η : ℕ → Ω → ℝ)
    (I : ℕ → Ω → Fin d) (i : Fin d) (t : ℕ) (ω : Ω) : ℝ :=
  (∑ s ∈ (Finset.range t).filter (fun s => I (s + 1) ω = i), (μ (I (s + 1) ω) + η (s + 1) ω))
    / (pullCount I i t ω : ℝ)

/-- The pseudo-regret `R_n = ∑_{t=1}^n (μ_* - μ_{I_t})` after `n` rounds (§1.2, pp. 2–3, in the
`d`-armed special case of §6, where the decision set is the standard basis). `R_0 = 0`. -/
noncomputable def pseudoRegret {Ω : Type*} {d : ℕ} (μ : Fin d → ℝ) (I : ℕ → Ω → Fin d)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range n, (bestMean μ - μ (I (t + 1) ω))

/-- The confidence width `c_{i,t}` of eq. (3), p. 7, as a function of the pull count
`N = N_{i,t}`:
`√((1 + N) / N² · (1 + 2 log(d (1 + N)^{1/2} / δ)))`.
At `N = 0` the paper's value is `+∞`; here it is the junk value `0` (division by zero), so every
statement using it treats `N = 0` separately. -/
noncomputable def confRadius (d : ℕ) (δ : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt ((1 + (N : ℝ)) / (N : ℝ) ^ 2 *
    (1 + 2 * Real.log ((d : ℝ) * Real.sqrt (1 + (N : ℝ)) / δ)))

end ImprovedLinBandits.UCBDelta


