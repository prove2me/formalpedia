-- Prove2me | Definitions.Def_BwSC_LowerBound_Model
-- name    : BwSC_LowerBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:27.250779+00:00
-- url     : https://prove2.me/theorems/1d45950d-af09-4643-bb5b-29a295c22328
-- title:
--   §1.2, Definition 1, §3, pp. 3–4, 11, 14, 17, 21 — unit-cost switching count, the class Π_S of S-switch policies, q(S,K), r(S,K) and the two rates of Theorem 2
-- statement:
--   A learner plays a $K$-armed bandit for $T$ rounds. In round $t\in[T]$ it chooses an action $a_t\in[K]$ and observes a reward drawn from the distribution of that arm. A policy $\pi$ is a sequence of Markov kernels choosing $a_{t+1}$ from the history $\big((a_1,X_1),\dots,(a_t,X_t)\big)$; under the unit-variance Gaussian environment with mean vector $\mu\in\mathbb R^K$ (arm $i$ pays $\mathcal N(\mu_i,1)$), the law of the $T$-round history is $\mathbb P^\pi_\mu$ and the regret is $R^\pi_\mu(T)=T\mu^*-\mathbb E^\pi_\mu[\sum_{t=1}^T X_t]$ with $\mu^*=\max_i\mu_i$ (published definitions `BanditPolicy`, `banditRegret`, `GaussianBandit`).
--
--   This file defines the switching-constrained model of §3 (unit switching costs $c_{i,j}=1$ for $i\neq j$).
--
--   1. **Switching cost of a period.** For $n_1,n_2\in\mathbb N$, $S(n_1:n_2)$ is the number of rounds $t$ with $n_1\le t$, $t+1\le n_2$ and $a_t\neq a_{t+1}$; a switch between round $n_1-1$ and $n_1$, or between $n_2$ and $n_2+1$, is not counted (App. J.1, p. 60). The total number of switches is $S(1:T)=\sum_{t=1}^{T-1}\mathbb 1\{a_t\neq a_{t+1}\}$.
--   2. **$S$-switch policies.** For $S\in\mathbb N$, $\pi\in\Pi_S$ when for every mean vector $\mu\in\mathbb R^K$,
--   $$\mathbb P^\pi_\mu\Big[\sum_{t=1}^{T-1}\mathbb 1\{a_t\neq a_{t+1}\}\le S\Big]=1 .$$
--   3. **Phase index and remainder.** $q(S,K)=\lfloor (S-1)/(K-1)\rfloor$ with $\lfloor x\rfloor=0$ for $x<0$, and $r(S,K)=S-1-q(S,K)(K-1)$, an integer: $r(S,K)=(S-1)\,\%\,(K-1)$ for $S\ge1$ and $r(0,K)=-1$.
--   4. **Rates.** With $a(q)=1/(2-2^{-q})$,
--   $$A(K,S,T)=\frac{(K-r(S,K))^{2-a(q(S,K))}}{K}\,T^{a(q(S,K))},\qquad B(K,S,T)=K^{1-a(q(S,K)+1)}\,T^{a(q(S,K)+1)} .$$
--
--   These objects state Theorem 2 and the reduction on p. 59; every statement of the mission uses them.
--
--   **Formalization Note** Rounds are 1-based as on the page: entry $s$ of a history $h\in(\{1,\dots,K\}\times\mathbb R)^T$ is round $s+1$, and a period $[n_1:n_2]$ is the set of rounds $t$ with $n_1\le t\le n_2$ and $1\le t\le T$. The action of round $t$ is an `Option`, `none` outside $1\le t\le T$, so periods starting at round $0$ read as starting at round $1$. Definition 1 asks the budget to hold almost surely for *every* sub-Gaussian environment; here it is asked only for the unit-variance Gaussian environments, which is a weaker requirement on the policy (so results quantifying over $\Pi_S$ become stronger), and is exactly the class used in the proof of Theorem 2 (p. 59: "we focus on the setting of $\mathcal D_k=\mathcal N(\mu_k,1)$"). The budget $S$ is a natural number (§3, p. 14). $q$ and $r$ are written with the explicit case $S=0$, never with integer division of $-1$. All powers are real powers of positive reals.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, pp. 3–4 (§1.2, Definition 1), p. 11 (§1.4), p. 14 (§3), p. 17 (§3.2), p. 21 (Theorem 2), p. 60 (App. J.1, item 1)

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_banditRegret
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BwSC.LowerBound

/-- The vector of actions `(a_1, …, a_T)` of a `T`-round history
(Simchi-Levi & Xu, arXiv:1905.10825v4, §1.2, p. 3). Entry `s : Fin T` is the arm played in
the 1-based round `s + 1`. -/
def actions {K T : ℕ} (h : BanditHistory K T) : Fin T → Fin K := fun s => (h s).1

/-- The action of the **1-based** round `t` read off an action vector: `some a_t` when
`1 ≤ t ≤ T`, and `none` for every other `t` (round `0` and rounds after `T` do not exist). -/
def actA {K T : ℕ} (a : Fin T → Fin K) (t : ℕ) : Option (Fin K) :=
  if ht : 1 ≤ t ∧ t ≤ T then some (a ⟨t - 1, by omega⟩) else none

/-- The action `a_t` of the 1-based round `t` of a history (`none` outside `1 ≤ t ≤ T`). -/
def act {K T : ℕ} (h : BanditHistory K T) (t : ℕ) : Option (Fin K) :=
  actA (actions h) t

/-- The unit switching cost `S(n₁ : n₂)` of the period `[n₁ : n₂]` (App. J.1, item 1, p. 60,
with unit costs `c_{i,j} = 1` for `i ≠ j`, §3, p. 14): the number of 1-based rounds `t` with
`n₁ ≤ t`, `t + 1 ≤ n₂`, `1 ≤ t`, `t + 1 ≤ T` and `a_t ≠ a_{t+1}`. A switch between round
`n₁ - 1` and `n₁`, or between `n₂` and `n₂ + 1`, is not counted. -/
def switchCost {K T : ℕ} (h : BanditHistory K T) (n₁ n₂ : ℕ) : ℕ :=
  ((Finset.range (T + 1)).filter
    (fun t => n₁ ≤ t ∧ t + 1 ≤ n₂ ∧ 1 ≤ t ∧ t + 1 ≤ T ∧ act h t ≠ act h (t + 1))).card

/-- The class `Π_S` of `S`-switch policies (Definition 1, p. 4, with unit costs, §3, p. 14):
a policy is admissible when, under every unit-variance Gaussian environment `N(μ_i, 1)`, its
total number of switches `Σ_{t=1}^{T-1} 1{a_t ≠ a_{t+1}}` over the horizon `T` is at most `S`
almost surely. -/
def IsSwitchPolicy {K : ℕ} (S T : ℕ) (π : BanditPolicy K) : Prop :=
  ∀ μvec : Fin K → ℝ,
    ∀ᵐ h ∂(banditMeasure (gaussianBandit μvec) π T), switchCost h 1 T ≤ S

/-- `q(S, K) = ⌊(S - 1)/(K - 1)⌋` (Theorem 2, p. 21), with the paper's convention
`⌊x⌋ = 0` for `x < 0` (§1.4, p. 11), so `q(0, K) = 0`. -/
def qIdx (S K : ℕ) : ℕ := if S = 0 then 0 else (S - 1) / (K - 1)

/-- `r(S, K) = S - 1 - q(S, K)(K - 1)` (§3.2, p. 17), an integer: it equals
`(S - 1) % (K - 1)` for `S ≥ 1` and `-1` for `S = 0`. -/
def rIdx (S K : ℕ) : ℤ := (S : ℤ) - 1 - (qIdx S K : ℤ) * ((K : ℤ) - 1)

/-- The exponent `1/(2 - 2^{-q})` of Theorem 2, p. 21. -/
noncomputable def aExp (q : ℕ) : ℝ := 1 / (2 - (2 : ℝ) ^ (-(q : ℝ)))

/-- The first rate of Theorem 2, p. 21:
`((K - r(S,K))^{2 - 1/(2 - 2^{-q(S,K)})} / K) · T^{1/(2 - 2^{-q(S,K)})}`. -/
noncomputable def rateA (K S T : ℕ) : ℝ :=
  ((K : ℝ) - (rIdx S K : ℝ)) ^ (2 - aExp (qIdx S K)) / K * (T : ℝ) ^ aExp (qIdx S K)

/-- The second rate of Theorem 2, p. 21:
`K^{1 - 1/(2 - 2^{-q(S,K)-1})} · T^{1/(2 - 2^{-q(S,K)-1})}`. -/
noncomputable def rateB (K S T : ℕ) : ℝ :=
  (K : ℝ) ^ (1 - aExp (qIdx S K + 1)) * (T : ℝ) ^ aExp (qIdx S K + 1)

end BwSC.LowerBound


