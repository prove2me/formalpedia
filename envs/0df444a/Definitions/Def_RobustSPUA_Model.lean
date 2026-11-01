-- Prove2me | Definitions.Def_RobustSPUA_Model
-- name    : RobustSPUA_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:41.490506+00:00
-- url     : https://prove2.me/theorems/f78be31d-41f6-4031-bb87-2e2bbb81f7f3
-- title:
--   The secretary problem with uncertain acceptance: outcome space, Markov randomized policies, occupation probabilities and the robust ratio $\gamma_{\mathcal P}$
-- statement:
--   These are the objects of the **secretary problem with uncertain acceptance** (SP-UA) of Perez-Salazar, Singh and Toriello (§1.2, pp.3–4; §3, pp.9–10; Proposition 5, p.30).
--
--   There are $n\ge1$ candidates, totally ordered by quality, rank $1$ being the best. They arrive in a uniformly random order $\pi=(R_1,\dots,R_n)$, a permutation of $[n]=\{1,\dots,n\}$: $R_t$ is the (absolute) rank of the $t$-th arriving candidate. On arrival the decision maker (DM) observes only the **partial rank**
--   $$
--   r_t \;=\; 1+\#\{u<t:\ R_u<R_t\}\in[t],
--   $$
--   the rank of the $t$-th candidate among the first $t$ (so $r_t=1$ means best so far). The DM either passes or extends an offer; an offered candidate accepts with probability $p\in(0,1]$, which ends the process, and otherwise the DM moves on.
--
--   1. **Policies** (p.9). A randomized Markov policy is a map $q$ assigning to every state $(t,s)$, $t\in[n]$, $s\in[t]$, the probability $q(t,s)\in[0,1]$ of extending an offer when the $t$-th candidate has partial rank $s$. Deterministic policies are those with values in $\{0,1\}$.
--   2. **The probability space.** An outcome is $\omega=(\pi,o,a)$ with $\pi$ a permutation, $o\in\{0,1\}^n$ the offer coins and $a\in\{0,1\}^n$ the willingness coins; its probability is
--   $$
--   w(\omega)=\frac1{n!}\prod_{t=1}^n q(t,r_t)^{o_t}\bigl(1-q(t,r_t)\bigr)^{1-o_t}\prod_{t=1}^n p^{a_t}(1-p)^{1-a_t},
--   $$
--   and $\mathbf P(E)=\sum_{\omega\in E}w(\omega)$. The candidate at time $t$ accepts an offer iff $a_t=1$.
--   3. **Events** (pp.9–10, 30). The policy *reaches* time $t$ if no earlier candidate received an offer and accepted it. It *reaches state $(t,s)$ and selects the candidate* if it reaches time $t$, $r_t=s$ and $o_t=1$; it *does not select* if instead $o_t=0$. The occupation probabilities are
--   $$
--   x_{t,s}=\mathbf P(\text{reach }(t,s),\ \text{select}),\qquad y_{t,s}=\mathbf P(\text{reach }(t,s),\ \text{pass}).
--   $$
--   The policy *collects a top $k$ candidate* if it reaches some time $t$, extends an offer, the candidate accepts, and $R_t\le k$. *At least one of the top $k$ candidates accepts* if $a_t=1$ for some $t$ with $R_t\le k$.
--   4. **Robust ratio** (1), p.4:
--   $$
--   \gamma_{\mathcal P}=\min_{k=1,\dots,n}\frac{\mathbf P(\mathcal P\text{ collects a top }k\text{ candidate})}{\mathbf P(\text{at least one of the top }k\text{ candidates accepts})},\qquad \gamma^*_n=\sup_{\mathcal P}\gamma_{\mathcal P}.
--   $$
--   5. **Conditional rank probability** (Theorem 2, p.5): $\mathbf P(R_t\le k\mid r_t=s)$ under the uniform permutation.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Arrival times are `Fin n` (0-based): Lean's time `t` is the paper's $t+1$, and the absolute rank is `π t + 1`, so "top $k$" is `(π t).val < k`. A policy is `q : ℕ → ℕ → ℝ` read at the paper's 1-based state, and `IsPolicy n q` asks $q(t,s)\in[0,1]$ on the state space; values elsewhere are never read. `robustRatio` is the infimum over `k : Fin n` (a minimum for $n\ge1$), and `robustRatios n p` is the set of robust ratios of all policies. `condRankProb n t s k` is the count ratio $\#\{\pi: r_t=s,\ R_t\le k\}/\#\{\pi: r_t=s\}$. Events use classical decidability.
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, §1.2, pp.3–4 (model, robust ratio (1)); §3, pp.9–10 (states, policies, randomized policies, reaches, collects); Proposition 5, p.30 (x_{t,s}, y_{t,s}); Theorem 2, p.5 (P(R_t ≤ k | r_t = s))

import Mathlib

open Finset

namespace RobustSPUA

/-! # The secretary problem with uncertain acceptance (SP-UA): process, policies, robust ratio

S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer
Acceptance*, arXiv:2112.00842v2: §1.2, pp.3–4 (model, robust ratio (1)); §3, pp.9–10 (states,
Markov randomized policies, "reaches", "collects"); Proposition 5, p.30 (occupation
probabilities `x_{t,s}`, `y_{t,s}`); Theorem 2, p.5 (`P(R_t ≤ k | r_t = s)`).

**Formalization Note**
* Times are 0-based (`t : Fin n`); the paper's time is `t.val + 1`. The arrival order is a
  permutation `π : Equiv.Perm (Fin n)`, uniformly distributed; the candidate arriving at time `t`
  has absolute rank `R = (π t).val + 1` (rank 1 = best), so "top `k`" is `(π t).val < k`. Its
  partial rank is `1 + #{u < t : π u < π t}` (1 = best so far).
* A (randomized, Markov) policy is `q : ℕ → ℕ → ℝ`, read at the paper's 1-based state `(t, s)`;
  `q t s` is the probability of extending an offer. `IsPolicy n q` asks `q t s ∈ [0,1]` for
  `t ∈ [n]`, `s ∈ [t]`; values off the state space are never read. Deterministic policies are the
  `{0,1}`-valued ones.
* The randomness is encoded on the finite space `Ω_n = Perm(Fin n) × Bool^n × Bool^n`,
  `ω = (π, o, a)`: `π` is uniform; given `π`, the offer coins `o t` are independent
  Bernoulli(`q (t+1) (r_t)`); the willingness coins `a t` are i.i.d. Bernoulli(`p`), independent
  of everything else, and candidate `t` accepts an offer iff `a t`. The weight `weight n p q ω` is
  the product of these probabilities. Coins after the process stops affect no event.
* Decidability of events is classical. -/

/-- The finite outcome space `Perm(Fin n) × (Fin n → Bool) × (Fin n → Bool)`: arrival order,
offer coins, willingness-to-accept coins. -/
abbrev Outcome (n : ℕ) : Type := Equiv.Perm (Fin n) × (Fin n → Bool) × (Fin n → Bool)

/-- The partial rank `r_t ∈ [t]` (p.3) of the candidate arriving at (0-based) time `t`:
`1 +` the number of earlier candidates ranked better (1 = best so far). -/
def partialRank {n : ℕ} (π : Equiv.Perm (Fin n)) (t : Fin n) : ℕ :=
  1 + (univ.filter (fun u : Fin n => u < t ∧ π u < π t)).card

/-- A randomized Markov policy (p.9): at the 1-based state `(t, s)`, `t ∈ [n]`, `s ∈ [t]`, it
offers with probability `q t s ∈ [0,1]`. -/
def IsPolicy (n : ℕ) (q : ℕ → ℕ → ℝ) : Prop :=
  ∀ t ∈ Icc 1 n, ∀ s ∈ Icc 1 t, 0 ≤ q t s ∧ q t s ≤ 1

/-- The probability weight of an outcome `(π, o, a)` under policy `q` and acceptance
probability `p`: `π` uniform (`1/n!`), offer coin at time `t` with probability
`q (t+1) (r_t)`, acceptance coin with probability `p`, all independent given `π`. -/
noncomputable def weight (n : ℕ) (p : ℝ) (q : ℕ → ℕ → ℝ) (ω : Outcome n) : ℝ :=
  (1 / (n.factorial : ℝ)) *
    (∏ t : Fin n, if ω.2.1 t then q (t.val + 1) (partialRank ω.1 t)
      else 1 - q (t.val + 1) (partialRank ω.1 t)) *
    ∏ t : Fin n, if ω.2.2 t then p else 1 - p

open Classical in
/-- The probability of an event `E ⊆ Ω_n` under policy `q` and acceptance probability `p`. -/
noncomputable def prob (n : ℕ) (p : ℝ) (q : ℕ → ℕ → ℝ) (E : Outcome n → Prop) : ℝ :=
  ∑ ω : Outcome n, if E ω then weight n p q ω else 0

/-- The policy reaches (0-based) stage `t` (p.9): no earlier candidate received an offer and
accepted it. -/
def reaches {n : ℕ} (ω : Outcome n) (t : Fin n) : Prop :=
  ∀ u : Fin n, u < t → ¬ (ω.2.1 u = true ∧ ω.2.2 u = true)

/-- The policy reaches the 1-based state `(t, s)` and selects (extends an offer to) the
candidate (Proposition 5, p.30). -/
def offersAt {n : ℕ} (t s : ℕ) (ω : Outcome n) : Prop :=
  ∃ t₀ : Fin n, t₀.val + 1 = t ∧ reaches ω t₀ ∧ partialRank ω.1 t₀ = s ∧ ω.2.1 t₀ = true

/-- The policy reaches the 1-based state `(t, s)` and does not select the candidate
(Proposition 5, p.30). -/
def passesAt {n : ℕ} (t s : ℕ) (ω : Outcome n) : Prop :=
  ∃ t₀ : Fin n, t₀.val + 1 = t ∧ reaches ω t₀ ∧ partialRank ω.1 t₀ = s ∧ ω.2.1 t₀ = false

/-- `x_{t,s} = P(P reaches state (t,s), selects candidate)` (Proposition 5, p.30). -/
noncomputable def occX (n : ℕ) (p : ℝ) (q : ℕ → ℕ → ℝ) (t s : ℕ) : ℝ :=
  prob n p q (offersAt t s)

/-- `y_{t,s} = P(P reaches state (t,s), does not select candidate)` (Proposition 5, p.30). -/
noncomputable def occY (n : ℕ) (p : ℝ) (q : ℕ → ℕ → ℝ) (t s : ℕ) : ℝ :=
  prob n p q (passesAt t s)

/-- The policy collects a top `k` candidate (p.10): it reaches some stage `t`, extends an offer
to the candidate there, the candidate accepts, and the candidate's absolute rank is `≤ k`. -/
def collectsTop {n : ℕ} (k : ℕ) (ω : Outcome n) : Prop :=
  ∃ t : Fin n, reaches ω t ∧ ω.2.1 t = true ∧ ω.2.2 t = true ∧ (ω.1 t).val < k

/-- At least one of the top `k` candidates accepts an offer (denominator of (1), p.4): some
candidate of absolute rank `≤ k` is willing to accept. -/
def topAccepts {n : ℕ} (k : ℕ) (ω : Outcome n) : Prop :=
  ∃ t : Fin n, (ω.1 t).val < k ∧ ω.2.2 t = true

/-- The robust ratio (1), p.4:
`γ_q = min_{k ∈ [n]} P(q collects a top k candidate) / P(some top k candidate accepts)`.
(For `n ≥ 1` the infimum over the finite nonempty index set is a minimum.) -/
noncomputable def robustRatio (n : ℕ) (p : ℝ) (q : ℕ → ℕ → ℝ) : ℝ :=
  ⨅ k : Fin n, prob n p q (collectsTop (k.val + 1)) / prob n p q (topAccepts (k.val + 1))

/-- The set of robust ratios of all randomized Markov policies; `γ*_n` is its supremum (p.4). -/
def robustRatios (n : ℕ) (p : ℝ) : Set ℝ :=
  {r | ∃ q, IsPolicy n q ∧ r = robustRatio n p q}

/-- The conditional probability `P(R_t ≤ k | r_t = s)` under the uniform arrival permutation
(Theorem 2, p.5), for the 1-based time `t`: the number of permutations in which the `t`-th
candidate has partial rank `s` and absolute rank `≤ k`, divided by the number in which it has
partial rank `s`. -/
noncomputable def condRankProb (n t s k : ℕ) : ℝ :=
  ((univ.filter (fun π : Equiv.Perm (Fin n) =>
      ∃ t₀ : Fin n, t₀.val + 1 = t ∧ partialRank π t₀ = s ∧ (π t₀).val < k)).card : ℝ) /
  ((univ.filter (fun π : Equiv.Perm (Fin n) =>
      ∃ t₀ : Fin n, t₀.val + 1 = t ∧ partialRank π t₀ = s)).card : ℝ)

end RobustSPUA


