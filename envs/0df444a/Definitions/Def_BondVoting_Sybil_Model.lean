-- Prove2me | Definitions.Def_BondVoting_Sybil_Model
-- name    : BondVoting_Sybil_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:07.730412+00:00
-- url     : https://prove2.me/theorems/ca52ab16-d8ce-4e14-a8d6-09518e29ffdb
-- title:
--   §2–§3.2, pp. 10–23 — vote-function properties, Sybil attacks, Sybil resistance, robust v-implementability; voting bonds and the bond-voting payoff
-- statement:
--   This file sets up the model of voting with time commitment of Mohan, Khezr and Berg and the bond-voting mechanism.
--
--   **Vote functions.** A *vote function* $v(q, t)$ turns a stake of $q$ tokens committed for $t$ units of time into a number of votes, on a platform with maximal commitment horizon $T$.
--
--   1. $v$ *values commitment* (Definition 2) if $\partial v(q,t)/\partial t > 0$ for every $q > 0$ and $t \in (0, T]$.
--   2. $v$ has *non-increasing influence of tokens* (Definition 3) if $\partial v(q,t)/\partial q > 0$ and $\partial^2 v(q,t)/\partial q^2 \le 0$ for every $q > 0$ and $t \in (0, T]$.
--
--   **Sybil attacks.** An agent with budget $q$ and payoff function $\pi(q, t)$ may split her budget over $M$ identities, with stakes $q_1, \dots, q_M$ and commitments $t_1, \dots, t_M$. The attack is *feasible* (Definition 5(a)–(b)) if $q_m \ge 0$, $\sum_{m=1}^M q_m \le q$ and $t_m \in (0, T]$ for every $m$. Its payoff is the total payoff of the identities,
--   $$\pi(q_1, \dots, q_M; t_1, \dots, t_M) = \sum_{m=1}^{M} \pi(q_m, t_m).$$
--   It is *profitable* (Definition 5(c)) if this payoff is strictly larger than $\pi(q, t)$ for every commitment $t \in [0, T]$ the agent could choose acting as a single entity. A payoff function is *Sybil resistant* (Definition 6) if for no budget $q > 0$ there is a feasible and profitable attack. A mechanism with vote function $v$ and a class of agent payoff functions is *robustly v-implementable* (Definition 7) if $v$ values commitment, has non-increasing influence of tokens, and every payoff function in the class is Sybil resistant.
--
--   **Bond voting.** The platform sets a voting bond rate $r$. A $t$-bond costs $P_t = e^{-rt}$ tokens (equation (3)) and carries one vote, so a budget $q$ buys
--   $$V = v(q, t) = \frac{q}{P_t} \quad (t > 0), \qquad v(q, 0) = 0$$
--   votes. An agent of type $(\theta, u, r_i)$ — marginal pivotality $\theta$, value $u$ of the policy, outside return $r_i$ — has payoff (equation (4))
--   $$\pi_i(q, t) = |u|\theta V - V P_t\,(e^{r_i t} - 1) \quad (t > 0), \qquad \pi_i(q, 0) = 0.$$
--   An agent type is *admissible* if $|u|\theta > 1$ (p. 22) and $r_i > r$ (Proposition 1). Finally, $t^*_i$ is the optimal bond length of equation (6), transcribed as printed:
--   $$t^*_i = \begin{cases} T & \text{if } r_i \le \frac{\theta|u|}{e^{T(r_i - r)}}\, r,\\ \frac{\ln(\theta|u| r / r_i)}{r_i - r} & \text{if } \frac{\theta|u|}{e^{T(r_i - r)}}\, r < r_i < \theta|u| r,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   These objects are shared by every statement of the mission: Theorem 1, Proposition 1 and Proposition 2 are all phrased in them.
--
--   **Formalization Note.** Derivatives in Definitions 2–3 are given by `HasDerivAt` witnesses (the second derivative is the derivative of a function that is $\partial v/\partial q$ on a neighbourhood), so a non-differentiable vote function cannot satisfy them by a default value. The page leaves the attack payoff $\pi_i(q_{i1},\dots;t_{i1},\dots)$ and the single-entity commitment in Definition 5(c) implicit; the sum over identities is the paper's own computation (pp. 16, 25), and comparing against every $t \in [0, T]$ (the agent's choice set, p. 10) is the reading under which both the "if" half of Theorem 1 and Proposition 2 hold. Identities with zero stake are allowed, and $M = 0$ is allowed (the empty attack has payoff $0$). The payoff is $0$ at $t = 0$ as the paper imposes, so it is discontinuous at $t = 0$; the agent always buys $V = q/P_t$ votes, as on p. 22.
-- source:
--   Mohan, Khezr & Berg, Voting with time commitment for decentralized governance: Bond voting as a Sybil-resistant mechanism, SSRN 4259599 (PDF of 2024-02-20), pp. 10–23, Definitions 1–3, 5–7, equations (1), (3), (4), (6)

import Mathlib

namespace BondVoting.Sybil

/-- Definition 2 (valuable commitment), p. 11: `∂v(q,t)/∂t > 0` for every `q > 0` and
`t ∈ (0, T]`, with the derivative given by a `HasDerivAt` witness. -/
def ValuableCommitment (v : ℝ → ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ q : ℝ, 0 < q → ∀ t ∈ Set.Ioc 0 T, ∃ d : ℝ, HasDerivAt (fun s => v q s) d t ∧ 0 < d

/-- Definition 3 (non-increasing influence of tokens), p. 11: `∂v/∂q > 0` and
`∂²v/∂q² ≤ 0` for every `q > 0` and `t ∈ (0, T]`. `v'` is `∂v/∂q` on a neighbourhood of `q`,
so the second derivative is a genuine derivative of the first. -/
def NonIncreasingInfluence (v : ℝ → ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ q : ℝ, 0 < q → ∀ t ∈ Set.Ioc 0 T, ∃ (v' : ℝ → ℝ) (d2 : ℝ),
    (∀ᶠ x in nhds q, HasDerivAt (fun y => v y t) (v' x) x) ∧ 0 < v' q ∧
    HasDerivAt v' d2 q ∧ d2 ≤ 0

/-- Definition 5 (a)–(b), p. 13: an `M`-identity attack with budget profile `qs` and time
profile `ts` is feasible for an agent with budget `q` if the stakes are non-negative, sum to at
most `q`, and every commitment lies in `(0, T]`. -/
def FeasibleAttack (q T : ℝ) (M : ℕ) (qs ts : Fin M → ℝ) : Prop :=
  (∀ m, 0 ≤ qs m) ∧ ∑ m, qs m ≤ q ∧ ∀ m, ts m ∈ Set.Ioc 0 T

/-- The attack payoff `π_i(q_i1,…,q_iM; t_i1,…,t_iM)` of Definition 5(c): the sum of the
identities' payoffs, as computed in the proofs on pp. 16 and 25. -/
def attackPayoff (π : ℝ → ℝ → ℝ) {M : ℕ} (qs ts : Fin M → ℝ) : ℝ :=
  ∑ m, π (qs m) (ts m)

/-- Definition 5, p. 13: a feasible and profitable Sybil attack. Profitable means that the attack
payoff strictly exceeds the payoff of every single-entity choice `t ∈ [0, T]` with the whole
budget `q`. -/
def ProfitableAttack (π : ℝ → ℝ → ℝ) (q T : ℝ) (M : ℕ) (qs ts : Fin M → ℝ) : Prop :=
  FeasibleAttack q T M qs ts ∧ ∀ t ∈ Set.Icc 0 T, π q t < attackPayoff π qs ts

/-- Definition 6, p. 14, for an agent with payoff function `π`: for no budget `q > 0` is there a
feasible and profitable Sybil attack. -/
def SybilResistant (π : ℝ → ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ q : ℝ, 0 < q → ∀ (M : ℕ) (qs ts : Fin M → ℝ), ¬ ProfitableAttack π q T M qs ts

/-- Definition 7, p. 14: the vote function `v` values commitment and has non-increasing influence
of tokens, and every agent payoff function in `payoffs` is Sybil resistant. -/
def RobustlyVImplementable (v : ℝ → ℝ → ℝ) (payoffs : Set (ℝ → ℝ → ℝ)) (T : ℝ) : Prop :=
  ValuableCommitment v T ∧ NonIncreasingInfluence v T ∧ ∀ π ∈ payoffs, SybilResistant π T

/-- Equation (3), p. 20: the price `P_t = e^{-rt}` of a `t`-bond at the voting bond rate `r`. -/
noncomputable def bondPrice (r t : ℝ) : ℝ := Real.exp (-(r * t))

/-- The bond vote function, p. 22: `V = q / P_t` votes for `t > 0`, and `V = 0` at `t = 0`. -/
noncomputable def bondVote (r q t : ℝ) : ℝ := if 0 < t then q / bondPrice r t else 0

/-- Equation (4), p. 22, with `V = q / P_t`: `π = |u| θ V − V P_t (e^{r_i t} − 1)` for `t > 0`,
and `π = 0` at `t = 0`. -/
noncomputable def bondPayoff (r θ u ri q t : ℝ) : ℝ :=
  if 0 < t then
    |u| * θ * bondVote r q t - bondVote r q t * bondPrice r t * (Real.exp (ri * t) - 1)
  else 0

/-- The standing assumptions on an agent type: `|u| θ > 1` (p. 22) and `r_i > r`
(Proposition 1, p. 23). -/
def Admissible (r θ u ri : ℝ) : Prop := 1 < |u| * θ ∧ r < ri

/-- The payoff functions `(q, t) ↦ π_i(q, t)` of all admissible agents under bond voting. -/
def bondPayoffs (r : ℝ) : Set (ℝ → ℝ → ℝ) :=
  {π | ∃ θ u ri : ℝ, Admissible r θ u ri ∧ π = bondPayoff r θ u ri}

/-- Equation (6), p. 23, as printed: the optimal bond length `t*_i`. -/
noncomputable def tStar (r θ u ri T : ℝ) : ℝ :=
  if ri ≤ θ * |u| / Real.exp (T * (ri - r)) * r then T
  else if ri < θ * |u| * r then Real.log (θ * |u| * r / ri) / (ri - r) else 0

end BondVoting.Sybil


