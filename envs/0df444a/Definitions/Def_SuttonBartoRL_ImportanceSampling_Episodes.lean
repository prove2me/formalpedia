-- Prove2me | Definitions.Def_SuttonBartoRL_ImportanceSampling_Episodes
-- name    : SuttonBartoRL_ImportanceSampling_Episodes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:29:55.966032+00:00
-- url     : https://prove2.me/theorems/60fd6f9d-aeda-4431-ab45-b025ed935e02
-- title:
--   Episodes, returns, importance-sampling ratios $\rho_{t:h}$, per-decision return $\tilde G_t$, and $v_\pi$
-- statement:
--   Fix a finite MDP with a set of terminal states and a start state $s$. An **episode of length** $n$ is a sequence
--
--   $$
--   S_0, A_0, R_1, S_1, A_1, R_2, \dots, A_{n-1}, R_n, S_n
--   $$
--
--   with rewards in $\mathcal R$. Under a policy $\mu$ it has probability
--
--   $$
--   \Pr_\mu(\text{episode}) = \prod_{k=0}^{n-1} \mu(A_k \mid S_k)\, p(S_{k+1}, R_{k+1} \mid S_k, A_k)
--   $$
--
--   if $S_0 = s$, the states $S_0, \dots, S_{n-1}$ are nonterminal and $S_n$ is terminal (so $T = n$ is the time of termination), and probability $0$ otherwise. The **state–action trajectory probability** is the same product with $p(S_{k+1} \mid S_k, A_k)$ in place of $p(S_{k+1}, R_{k+1} \mid S_k, A_k)$.
--
--   For a discount rate $\gamma$, the **return** is $G_0 = R_1 + \gamma R_2 + \dots + \gamma^{T-1} R_T$. For target and behaviour policies $\pi$ and $b$, the **importance-sampling ratio** of the first $j$ decisions is
--
--   $$
--   \rho_{0:j-1} = \prod_{k=0}^{\min(j, T)-1} \frac{\pi(A_k \mid S_k)}{b(A_k \mid S_k)},
--   $$
--
--   so $\rho_{0:T-1}$ is the full ratio, and the **per-decision return** is $\tilde G_0 = \rho_{0:0} R_1 + \gamma \rho_{0:1} R_2 + \dots + \gamma^{T-1} \rho_{0:T-1} R_T$.
--
--   The **expectation** of a function $X$ of the episode under $\mu$ from $s$ is $\mathbb E_\mu[X \mid S_0 = s] = \sum_{n \ge 0} \sum_{\text{episodes of length } n} \Pr_\mu(\text{episode})\, X(\text{episode})$, and the **state value** is $v_\pi(s) = \mathbb E_\pi[G_0 \mid S_0 = s]$.
--
--   These definitions carry the chapter's off-policy prediction results: the ratio (5.3), the unbiasedness (5.4) and the per-decision estimator of §5.9 are statements about them.
--
--   **Formalization Note** Conditioning on $S_t = s$ is replaced by starting the episode at $S_0 = s$ (Markov property), so all times are shifted to $t = 0$. The reward $R_{j+1}$ is taken to be $0$ once the episode is over ($j \ge T$). The expectation is a series over episode lengths; Lean assigns the value $0$ to a divergent series, so the theorems add a termination hypothesis under which the series has finitely many nonzero terms. The ratio uses real division; a factor with $b(A_k \mid S_k) = 0$ gives $0$, but such episodes have probability $0$ under $b$. The value $v_\pi$ is defined from returns, not from a Bellman equation.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, episodes and returns §3.4, Eq. (3.11), pp. 54–57; v_π (3.12), p. 58; trajectory probability and Eq. (5.3), p. 104; per-decision return G̃_t, §5.9, p. 114

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_MDP

namespace SuttonBartoRL.ImportanceSampling

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]

/-- An episode of length `n` (§3.4, p. 54; §5.5, p. 104): states `S_0, …, S_n`, actions
`A_0, …, A_{n-1}` and rewards `R_1, …, R_n` drawn from the finite reward set. The reward `R_{k+1}`
that follows action `A_k` is stored at index `k`. -/
abbrev Episode (M : MDP S A) (n : ℕ) : Type :=
  (Fin (n + 1) → S) × (Fin n → A) × (Fin n → M.R)

namespace Episode

variable {M : MDP S A} {n : ℕ}

/-- The state `S_k`, `k = 0, …, n`. -/
def states (e : Episode M n) : Fin (n + 1) → S := e.1

/-- The action `A_k`, `k = 0, …, n - 1`. -/
def actions (e : Episode M n) : Fin n → A := e.2.1

/-- The reward `R_{k+1}` that follows `A_k`, `k = 0, …, n - 1`. -/
def rewards (e : Episode M n) (k : Fin n) : ℝ := (e.2.2 k : ℝ)

/-- `R_{j+1}` for any `j : ℕ`, and `0` once the episode is over (`j ≥ n`). -/
def rewardAt (e : Episode M n) (j : ℕ) : ℝ :=
  if h : j < n then e.rewards ⟨j, h⟩ else 0

/-- The return `G_0 = R_1 + γ R_2 + ⋯ + γ^{T-1} R_T` of the episode, (3.11), p. 57, with `T = n`. -/
def ret (γ : ℝ) (e : Episode M n) : ℝ :=
  ∑ k : Fin n, γ ^ (k : ℕ) * e.rewards k

/-- The importance-sampling ratio (5.3), p. 104, of the first `j` decisions:
`ρ_{0:j-1} = Π_{k=0}^{j-1} π(A_k|S_k) / b(A_k|S_k)` (the product stops at `A_{n-1}`, so for
`j ≥ n` it is the full ratio `ρ_{0:T-1}`; for `j = 0` it is the empty product `1`). -/
noncomputable def isRatio (π b : SuttonBartoRL.FiniteMDP.Policy S A) (e : Episode M n) (j : ℕ) : ℝ :=
  ∏ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < j),
    π.prob (e.states k.castSucc) (e.actions k) / b.prob (e.states k.castSucc) (e.actions k)

/-- The per-decision importance-sampling return of §5.9, p. 114:
`G̃_0 = ρ_{0:0} R_1 + γ ρ_{0:1} R_2 + ⋯ + γ^{T-1} ρ_{0:T-1} R_T`. -/
noncomputable def perDecisionReturn (π b : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (e : Episode M n) : ℝ :=
  ∑ k : Fin n, γ ^ (k : ℕ) * e.isRatio π b ((k : ℕ) + 1) * e.rewards k

end Episode

/-- The probability, under policy `μ` and starting from `S_0 = s`, that the episode is exactly
`e`: `S_0 = s`, the states `S_0, …, S_{n-1}` are nonterminal, `S_n` is terminal (so `T = n` is the
time of termination), and the factors are `μ(A_k|S_k) p(S_{k+1}, R_{k+1} | S_k, A_k)`. If `s` is
terminal, the only episode of positive probability is the empty one (`n = 0`), with probability `1`. -/
def episodeProb (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) {n : ℕ}
    (e : Episode M n) : ℝ :=
  if e.states 0 = s ∧ (∀ k : Fin n, e.states k.castSucc ∉ term) ∧ e.states (Fin.last n) ∈ term then
    ∏ k : Fin n, μ.prob (e.states k.castSucc) (e.actions k) *
      M.p (e.states k.castSucc) (e.actions k) (e.states k.succ) (e.2.2 k : ℝ)
  else 0

/-- The probability of the state–action trajectory `A_0, S_1, A_1, …, S_n` from `S_0 = s` under `μ`
(p. 104): `Π_{k=0}^{n-1} μ(A_k|S_k) p(S_{k+1}|S_k, A_k)` with the three-argument `p` of (3.4), on
state sequences that start at `s`, stay nonterminal before `n` and are terminal at `n`; `0` on other
sequences. -/
def trajectoryProb (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) {n : ℕ}
    (st : Fin (n + 1) → S) (ac : Fin n → A) : ℝ :=
  if st 0 = s ∧ (∀ k : Fin n, st k.castSucc ∉ term) ∧ st (Fin.last n) ∈ term then
    ∏ k : Fin n, μ.prob (st k.castSucc) (ac k) * M.trans (st k.castSucc) (ac k) (st k.succ)
  else 0

/-- The expectation `E_μ[X | S_0 = s]` of a function `X` of the episode, for episodes generated by
policy `μ` from `S_0 = s` in the episodic MDP `(M, term)`: the sum over episode lengths `n` of the
(finite) sum over episodes of length `n` of probability times value. It is the book's expectation
whenever the series converges (in particular when episodes terminate within a bounded number of
steps); a non-summable series has the value `0` in Lean. -/
noncomputable def expectation (M : MDP S A) (term : Finset S) (μ : SuttonBartoRL.FiniteMDP.Policy S A) (s : S)
    (X : (n : ℕ) → Episode M n → ℝ) : ℝ :=
  ∑' n : ℕ, ∑ e : Episode M n, episodeProb M term μ s e * X n e

/-- The state value (3.12), p. 58, of an episodic task: `v_π(s) = E_π[G_0 | S_0 = s]`, the expected
return of an episode generated by `π` from `s`. -/
noncomputable def value (M : MDP S A) (term : Finset S) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (s : S) : ℝ :=
  expectation M term π s (fun _ e => e.ret γ)

end SuttonBartoRL.ImportanceSampling


