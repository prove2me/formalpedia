-- Prove2me | Definitions.Def_SuttonBartoRL_NStep_Trajectories
-- name    : SuttonBartoRL_NStep_Trajectories
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:37:57.172795+00:00
-- url     : https://prove2.me/theorems/59ddb304-511e-40b9-8201-afd331ddc585
-- title:
--   Trajectory distribution of $n$-step segments, the expected $n$-step return, and the off-policy returns (7.13)
-- statement:
--   Fix a finite MDP with dynamics $p(s', r \mid s, a)$ and a policy $\pi$. An **$n$-step segment** starting at time $t$ in state $S_t = s$ is the sequence of triples $(A_{t+k}, S_{t+k+1}, R_{t+k+1})$, $k = 0, \dots, n-1$, of actions, next states and rewards, with every reward in the finite reward set $\mathcal R$. When actions are drawn from $\pi$, the segment $\tau$ has conditional probability
--   $$\Pr_\pi(\tau \mid S_t = s) = \prod_{k=0}^{n-1} \pi(A_{t+k} \mid S_{t+k})\, p(S_{t+k+1}, R_{t+k+1} \mid S_{t+k}, A_{t+k}),$$
--   and the conditional expectation of a function $F$ of the segment is the finite sum $\mathbb E_\pi[F \mid S_t = s] = \sum_\tau \Pr_\pi(\tau \mid S_t = s)\, F(\tau)$. By the Markov property and stationarity it does not depend on $t$.
--
--   The file defines, along a segment:
--
--   1. the **$n$-step return** (7.1) for a fixed value estimate $V : \mathcal S \to \mathbb R$,
--   $$G_{t:t+n} = R_{t+1} + \gamma R_{t+2} + \cdots + \gamma^{n-1} R_{t+n} + \gamma^n V(S_{t+n}),$$
--   and its expectation $\mathbb E_\pi[G_{t:t+n} \mid S_t = s]$, the left-hand quantity of the error reduction property (7.3);
--   2. for a target policy $\pi$, a behavior policy $b$ and the per-decision ratios $\rho_t = \pi(A_t \mid S_t)/b(A_t \mid S_t)$, the **off-policy return with control variate** (7.13), defined recursively with horizon $h = t + n$ by
--   $$G_{t:h} = \rho_t\,(R_{t+1} + \gamma G_{t+1:h}) + (1 - \rho_t)\, V(S_t), \qquad G_{h:h} = V(S_h);$$
--   3. the **per-decision importance-sampled return** obtained from (7.13) by dropping the control variate, $G_{t:h} = \rho_t (R_{t+1} + \gamma G_{t+1:h})$, $G_{h:h} = V(S_h)$ — the "simple weighting" the book contrasts it with on p. 150.
--
--   **Formalization Note** The value estimate $V$ is a fixed function: in the algorithm it is the current estimate $V_{t+n-1}$ (or $V_{h-1}$), which is the same function for every step of one return. Where $b(A_t \mid S_t) = 0$, Lean's division gives $\rho_t = 0$; such segments have probability $0$ under $b$, so no expectation under $b$ depends on this value.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (7.1), p. 143; Eq. (7.3), p. 144; Eqs. (7.12)–(7.13) and the ratio ρ_t, p. 150

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_MDP

namespace SuttonBartoRL.NStep

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- An `n`-step trajectory segment that starts in a given state `S_t`: the `k`-th entry
(`k = 0, …, n − 1`) is the triple `(A_{t+k}, S_{t+k+1}, R_{t+k+1})` of the action taken, the next
state and the reward received, the reward ranging over the finite reward set `R` of the MDP. -/
abbrev Segment (M : MDP S A) (n : ℕ) : Type := Fin n → A × S × M.R

/-- The probability of an `n`-step segment `τ` given `S_t = s` when actions are drawn from the
policy `π`: the product `Π_{k<n} π(A_{t+k} | S_{t+k}) p(S_{t+k+1}, R_{t+k+1} | S_{t+k}, A_{t+k})`,
with `S_t = s` (§3.1 and §3.5, pp. 48 and 58). -/
def segmentProb (M : MDP S A) (π : Policy S A) : (n : ℕ) → S → Segment M n → ℝ
  | 0, _, _ => 1
  | n + 1, s, τ =>
      π.prob s (τ 0).1 * M.p s (τ 0).1 (τ 0).2.1 ((τ 0).2.2 : ℝ) *
        segmentProb M π n (τ 0).2.1 (Fin.tail τ)

/-- The states `S_t, S_{t+1}, …, S_{t+n}` visited by a segment `τ` started in `S_t = s`:
index `0` is `s`, index `k + 1` is the next state recorded in the `k`-th entry of `τ`. -/
def segmentStates (M : MDP S A) {n : ℕ} (s : S) (τ : Segment M n) : Fin (n + 1) → S :=
  Fin.cons s (fun k => (τ k).2.1)

/-- The conditional expectation `E_π[F | S_t = s]` of a function `F` of the next `n` steps,
given `S_t = s`, when actions are drawn from `π`: the finite sum
`Σ_τ Pr_π(τ | S_t = s) F(τ)` over all `n`-step segments. By the Markov property of the MDP and the
stationarity of `π`, it does not depend on `t`. -/
def segmentExpectation (M : MDP S A) (π : Policy S A) (n : ℕ) (s : S)
    (F : Segment M n → ℝ) : ℝ :=
  ∑ τ : Segment M n, segmentProb M π n s τ * F τ

/-- (7.1), p. 143: the `n`-step return along a segment started in `S_t = s`, bootstrapping from a
fixed value estimate `V : S → ℝ` (the book's `V_{t+n−1}`):
`G_{t:t+n} = R_{t+1} + γ R_{t+2} + ⋯ + γ^{n−1} R_{t+n} + γ^n V(S_{t+n})`. -/
def nStepReturnOn (M : MDP S A) (γ : ℝ) (V : S → ℝ) {n : ℕ} (s : S) (τ : Segment M n) : ℝ :=
  ∑ k : Fin n, γ ^ (k : ℕ) * ((τ k).2.2 : ℝ) + γ ^ n * V (segmentStates M s τ (Fin.last n))

/-- The expected `n`-step return `E_π[G_{t:t+n} | S_t = s]` of (7.3), p. 144, for a fixed value
estimate `V`, computed from the trajectory distribution of `π`. -/
def expectedNStepReturn (M : MDP S A) (π : Policy S A) (γ : ℝ) (V : S → ℝ) (n : ℕ) (s : S) : ℝ :=
  segmentExpectation M π n s (nStepReturnOn M γ V s)

/-- (7.13), p. 150: the off-policy `n`-step return with control variate along a segment started in
`S_t = s` whose actions were drawn from a behavior policy `b`, for a target policy `π` and a fixed
value estimate `V` (the book's `V_{h−1}`):
`G_{t:h} = ρ_t (R_{t+1} + γ G_{t+1:h}) + (1 − ρ_t) V(S_t)`, `G_{h:h} = V(S_h)`,
with `ρ_t = π(A_t | S_t) / b(A_t | S_t)`. Here `n = h − t`. -/
noncomputable def controlVariateReturnOn (M : MDP S A) (π b : Policy S A) (γ : ℝ) (V : S → ℝ) :
    (n : ℕ) → S → Segment M n → ℝ
  | 0, s, _ => V s
  | n + 1, s, τ =>
      (π.prob s (τ 0).1 / b.prob s (τ 0).1) *
          (((τ 0).2.2 : ℝ) + γ * controlVariateReturnOn M π b γ V n (τ 0).2.1 (Fin.tail τ)) +
        (1 - π.prob s (τ 0).1 / b.prob s (τ 0).1) * V s

/-- The per-decision importance-sampled `n`-step return obtained from (7.13), p. 150, by dropping
the control variate, i.e. by "simply weight[ing] the righthand side" of (7.12) (p. 150):
`G_{t:h} = ρ_t (R_{t+1} + γ G_{t+1:h})`, `G_{h:h} = V(S_h)`, with `ρ_t = π(A_t | S_t) / b(A_t | S_t)`. -/
noncomputable def perDecisionReturnOn (M : MDP S A) (π b : Policy S A) (γ : ℝ) (V : S → ℝ) :
    (n : ℕ) → S → Segment M n → ℝ
  | 0, s, _ => V s
  | n + 1, s, τ =>
      (π.prob s (τ 0).1 / b.prob s (τ 0).1) *
        (((τ 0).2.2 : ℝ) + γ * perDecisionReturnOn M π b γ V n (τ 0).2.1 (Fin.tail τ))

end SuttonBartoRL.NStep


