-- Prove2me | Definitions.Def_SuttonBartoRL_NStep_EpisodeReturns
-- name    : SuttonBartoRL_NStep_EpisodeReturns
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:38:08.760575+00:00
-- url     : https://prove2.me/theorems/17a8b7b7-539a-4b84-a5c7-bd8a1eb438b8
-- title:
--   Sample-path returns and TD errors of Chapter 7 (n-step, Sarsa, control-variate and tree-backup returns)
-- statement:
--   Fix one episode $S_0, A_0, R_1, S_1, A_1, R_2, \dots, R_T, S_T$ of length $T$, a discount $\gamma$, and value estimates that do not change during the episode. This file defines the returns of Chapter 7 along that episode.
--
--   1. The **complete return** $G_t = R_{t+1} + \gamma R_{t+2} + \cdots + \gamma^{T-t-1} R_T$ (p. 143).
--   2. The **$n$-step return** (7.1) with horizon $h = t + n$ and value estimate $V$: $G_{t:h} = \sum_{k=0}^{h-t-1} \gamma^k R_{t+k+1} + \gamma^{h-t} V(S_h)$ if $h < T$, and $G_{t:h} = G_t$ if $h \ge T$.
--   3. The **TD error** (6.5), $\delta_k = R_{k+1} + \gamma V(S_{k+1}) - V(S_k)$.
--   4. The **$n$-step Sarsa return** (7.4), $G_{t:t+n} = \sum_{k=0}^{n-1} \gamma^k R_{t+k+1} + \gamma^n Q_{t+n-1}(S_{t+n}, A_{t+n})$ if $t + n < T$ and $G_t$ otherwise, for action-value estimates $Q_k$ indexed by time $k \in \mathbb Z$ (so that the initial estimate $Q_{-1}$ exists), and the TD error of (7.6), $R_{k+1} + \gamma Q_k(S_{k+1}, A_{k+1}) - Q_{k-1}(S_k, A_k)$.
--   5. For a target policy $\pi$ and a behavior policy $b$, the **importance sampling ratio** $\rho_t = \pi(A_t \mid S_t)/b(A_t \mid S_t)$ and the **off-policy return with control variate** (7.13): $G_{t:h} = \rho_t(R_{t+1} + \gamma G_{t+1:h}) + (1 - \rho_t) V(S_t)$ for $t < h$, and $G_{h:h} = V(S_h)$.
--   6. The **expected approximate value** (7.8), $\bar V(s) = \sum_a \pi(a \mid s) Q(s, a)$, for fixed action values $Q$.
--   7. The **tree-backup return** (7.15)–(7.16) with horizon $h = t + n$: $G_{T-1:h} = R_T$; otherwise $G_{t:t+1} = R_{t+1} + \gamma \bar V(S_{t+1})$ for $n = 1$, and for $n \ge 2$
--   $$G_{t:t+n} = R_{t+1} + \gamma \sum_{a \ne A_{t+1}} \pi(a \mid S_{t+1}) Q(S_{t+1}, a) + \gamma\, \pi(A_{t+1} \mid S_{t+1})\, G_{t+1:t+n}.$$
--   8. The **expectation-based TD error** of Exercise 7.11, $\delta_k = R_{k+1} + \gamma \bar V(S_{k+1}) - Q(S_k, A_k)$.
--
--   These are the objects of the book's sum-of-TD-errors identities (Exercises 7.1, 7.4, 7.8, 7.11) and of the recursion (7.12).
--
--   **Formalization Note** The episode is given by sequences indexed by $\mathbb N$ together with the termination time $T$; entries after $T$ are never read at the indices the theorems allow. Values of the recursive returns outside the book's range ($t > h$, $t \ge T$, $n = 0$ for the tree backup) are fixed defaults that no theorem uses. The book's convention that terminal states have value $0$ (so $\bar V(S_T) = 0$, p. 148) is imposed in each theorem as a hypothesis on $V$ or $Q$ at $S_T$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (6.5), p. 121; Eq. (7.1), p. 143; Eqs. (7.4), p. 146, (7.6), (7.8), p. 148; Eq. (7.13), p. 150; Eqs. (7.15)–(7.16) and Exercise 7.11, p. 153

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_MDP

/-!
Sample-path returns of Chapter 7 of Sutton & Barto (2018), for one episode
`S_0, A_0, R_1, S_1, A_1, R_2, …, R_T, S_T` given as sequences: `St k = S_k`, `At k = A_k`,
`R k = R_k` (the value `R 0` is never used) and the termination time `T`. Entries after `T` are
never used by the book's formulas at the indices the theorems allow. Value estimates are fixed
functions (the book's "if the value estimates don't change").
-/

namespace SuttonBartoRL.NStep

variable {S A : Type}

/-- p. 143 (and (3.11), p. 57): the complete return of an episode that terminates at time `T`,
`G_t = R_{t+1} + γ R_{t+2} + ⋯ + γ^{T−t−1} R_T`. -/
def fullReturn (γ : ℝ) (R : ℕ → ℝ) (T t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (T - t), γ ^ k * R (t + k + 1)

/-- (7.1), p. 143, with horizon `h = t + n`: the truncated return
`G_{t:h} = R_{t+1} + γ R_{t+2} + ⋯ + γ^{h−t−1} R_h + γ^{h−t} V(S_h)` if `h < T`, and the complete
return `G_t` if `h ≥ T`, for a fixed value estimate `V : S → ℝ` (the book's `V_{h−1}`). -/
def nStepReturn (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (T : ℕ) (V : S → ℝ) (t h : ℕ) : ℝ :=
  if h < T then
    ∑ k ∈ Finset.range (h - t), γ ^ k * R (t + k + 1) + γ ^ (h - t) * V (St h)
  else fullReturn γ R T t

/-- (6.5), p. 121: the TD error `δ_k = R_{k+1} + γ V(S_{k+1}) − V(S_k)` for a fixed `V`. -/
def tdError (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (V : S → ℝ) (k : ℕ) : ℝ :=
  R (k + 1) + γ * V (St (k + 1)) - V (St k)

/-- (7.4), p. 146: the `n`-step Sarsa return
`G_{t:t+n} = R_{t+1} + γ R_{t+2} + ⋯ + γ^{n−1} R_{t+n} + γ^n Q_{t+n−1}(S_{t+n}, A_{t+n})` if
`t + n < T`, and `G_t` if `t + n ≥ T`. The action-value estimates `Q_k` are indexed by time
`k ∈ ℤ` so that the book's `Q_{−1}` (the initial estimate) is available. -/
def sarsaReturn (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (At : ℕ → A) (T : ℕ)
    (Q : ℤ → S → A → ℝ) (t n : ℕ) : ℝ :=
  if t + n < T then
    ∑ k ∈ Finset.range n, γ ^ k * R (t + k + 1) +
      γ ^ n * Q ((t : ℤ) + n - 1) (St (t + n)) (At (t + n))
  else fullReturn γ R T t

/-- The "novel TD error" in the brackets of (7.6), p. 148:
`R_{k+1} + γ Q_k(S_{k+1}, A_{k+1}) − Q_{k−1}(S_k, A_k)`. -/
def sarsaTDError (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (At : ℕ → A) (Q : ℤ → S → A → ℝ)
    (k : ℕ) : ℝ :=
  R (k + 1) + γ * Q (k : ℤ) (St (k + 1)) (At (k + 1)) - Q ((k : ℤ) - 1) (St k) (At k)

section Policies

variable [Fintype A]

/-- p. 150: the per-decision importance sampling ratio `ρ_t = π(A_t | S_t) / b(A_t | S_t)`. -/
noncomputable def isRatio (π b : Policy S A) (St : ℕ → S) (At : ℕ → A) (t : ℕ) : ℝ :=
  π.prob (St t) (At t) / b.prob (St t) (At t)

/-- (7.13), p. 150: the off-policy `n`-step return with control variate, ending at horizon `h`,
`G_{t:h} = ρ_t (R_{t+1} + γ G_{t+1:h}) + (1 − ρ_t) V(S_t)` for `t < h`, and `G_{h:h} = V(S_h)`,
for a fixed value estimate `V` (the book's `V_{h−1}`). The book uses it for `t < h < T`; the value
for `t > h` is `V(S_h)` and is never used. -/
noncomputable def controlVariateReturn (π b : Policy S A) (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (At : ℕ → A)
    (V : S → ℝ) (t h : ℕ) : ℝ :=
  if t < h then
    isRatio π b St At t * (R (t + 1) + γ * controlVariateReturn π b γ R St At V (t + 1) h) +
      (1 - isRatio π b St At t) * V (St t)
  else V (St h)
termination_by h - t

/-- (7.8), p. 148: the expected approximate value `V̄(s) = Σ_a π(a | s) Q(s, a)` of a state under
the target policy `π`, for fixed action-value estimates `Q`. -/
def expectedApproxValue (π : Policy S A) (Q : S → A → ℝ) (s : S) : ℝ :=
  ∑ a, π.prob s a * Q s a

variable [DecidableEq A]

/-- (7.15)–(7.16), p. 153: the tree-backup return `G_{t:h}` (horizon `h = t + n`) for fixed action
values `Q` and target policy `π`:
* `G_{T−1:h} = R_T` (the exception stated after (7.16));
* otherwise, for `n = 1` (`h = t + 1`), (7.15): `G_{t:t+1} = R_{t+1} + γ Σ_a π(a | S_{t+1}) Q(S_{t+1}, a)`;
* otherwise, for `n ≥ 2`, (7.16):
  `G_{t:h} = R_{t+1} + γ Σ_{a ≠ A_{t+1}} π(a | S_{t+1}) Q(S_{t+1}, a) + γ π(A_{t+1} | S_{t+1}) G_{t+1:h}`.
The values for `t ≥ T` and for `h ≤ t` are not defined by the book and are never used. -/
def treeBackupReturn (π : Policy S A) (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (At : ℕ → A) (T : ℕ)
    (Q : S → A → ℝ) (t h : ℕ) : ℝ :=
  if T ≤ t + 1 then R T
  else if h ≤ t + 1 then R (t + 1) + γ * expectedApproxValue π Q (St (t + 1))
  else
    R (t + 1) +
      γ * ∑ a ∈ Finset.univ.erase (At (t + 1)), π.prob (St (t + 1)) a * Q (St (t + 1)) a +
      γ * π.prob (St (t + 1)) (At (t + 1)) * treeBackupReturn π γ R St At T Q (t + 1) h
termination_by h - t

/-- p. 153, Exercise 7.11: the expectation-based TD error
`δ_k = R_{k+1} + γ V̄(S_{k+1}) − Q(S_k, A_k)`, with `V̄` from (7.8). -/
def expectedTDError (π : Policy S A) (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (At : ℕ → A)
    (Q : S → A → ℝ) (k : ℕ) : ℝ :=
  R (k + 1) + γ * expectedApproxValue π Q (St (k + 1)) - Q (St k) (At k)

end Policies

end SuttonBartoRL.NStep


