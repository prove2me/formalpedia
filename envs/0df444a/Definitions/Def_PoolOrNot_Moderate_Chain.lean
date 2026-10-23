-- Prove2me | Definitions.Def_PoolOrNot_Moderate_Chain
-- name    : PoolOrNot_Moderate_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:53.918823+00:00
-- url     : https://prove2.me/theorems/3ec6097d-86ee-439d-affb-7c0fa4d6ca5d
-- title:
--   §3, pp. 5–6 and (18), p. 7 — the DQ–JSQ chain with abandonment, q, q̄, r, the invariant state q*, p, and the metric d on ℝ^∞
-- statement:
--   The objects of the **DQ–JSQ system** (dedicated queues, join-the-shortest-queue) and of its fluid limit.
--
--   1. **The chain.** There are $n$ servers, each with its own FCFS queue. Customers arrive in a Poisson process of total rate $\lambda$, service times are exponential with mean $1/\mu$, and each waiting customer abandons after an exponential patience time with mean $1/\theta$. An arriving customer joins a server with the fewest customers. Let $Q_i$ be the number of servers with at least $i$ customers ($Q_0 = n$). The augmented queue length $Q = (Q_i)_{i \ge 1}$ is a continuous-time Markov chain with generator
--   $$\mathcal G f(Q) = \sum_{i \ge 0} \lambda\,\mathbf 1\{Q_1 = \dots = Q_i = n,\ Q_{i+1} < n\}\bigl(f(Q + e_{i+1}) - f(Q)\bigr) + \sum_{i \ge 1} \bigl(\mu + \theta(i-1)\bigr)(Q_i - Q_{i+1})\bigl(f(Q - e_i) - f(Q)\bigr).$$
--   The first sum is an arrival joining a server with exactly $i$ customers; the second is a service completion or an abandonment at one of the $Q_i - Q_{i+1}$ servers with exactly $i$ customers, each of which loses a customer at rate $\mu + \theta(i-1)$ (one in service, $i-1$ waiting).
--
--   2. **Fluid constants** (18). With $x^+ = \max(x, 0)$,
--   $$q := \frac{\mu(\rho - 1)^+}{\theta}, \qquad \bar q := \lfloor q \rfloor + 1, \qquad r := q - \lfloor q \rfloor .$$
--
--   3. **The invariant state** $q^* = (q^*_i)_{i \ge 1}$: $q^*_i = 1$ for $1 \le i \le \bar q$, $q^*_{\bar q + 1} = r$, and $q^*_i = 0$ for $i \ge \bar q + 2$.
--
--   4. **The mixing probability** of Theorem 4: $p := r(\mu + \theta \bar q)/(\rho\mu)$.
--
--   5. **The fluid-scaled state** $\bar Q^n = Q/n$ and the metric on $\mathbb R^\infty$
--   $$d(y, z) := \sum_{i=1}^\infty 2^{-i}\bigl(|y_i - z_i| \wedge 1\bigr).$$
--
--   These are shared by every statement of the mission: the chain carries the steady-state laws of Theorems 3–5, and $q, \bar q, r, q^*, p$ are the constants in which every limit is expressed.
--
--   **Formalization Note** The state space is the published `JSQHalfinWhitt.Tightness.State n`, which is 0-based: Lean `q.1 i` is the paper's $Q_{i+1}$, `ArrivesAt q i` says the arrival joins a server with exactly $i$ customers, and `down q i` removes a customer from a server with exactly $i+1$ customers, so the Lean departure rate is $\mu + \theta i$. The arrival rate in `genAb` is the total rate $\lambda$ (Braverman's published `genQ` uses $n\lambda$ and has no abandonment, and is not used). `qBar` is a natural number and the floor is `Nat.floor`, which equals the integer floor because $q \ge 0$. `qStar` and `fluidScaled` are indexed as in the paper ($i \ge 1$); their value at index $0$ is $1$ ($\bar Q_0 \equiv 1$), which `dInf` ignores.
-- source:
--   Cao, He, Huang & Liu, To Pool or Not to Pool: Queueing Design for Large-Scale Service Systems, Operations Research, Articles in Advance (2020), doi:10.1287/opre.2019.1976, pp. 5–8 (PDF 6–9), §3 (2)–(9), (18), §4.2 (q*), Theorem 4 (p), §4.3 (metric d)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Model
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary

open JSQHalfinWhitt.Tightness

namespace PoolOrNot.Moderate

open scoped Classical

/-- The generator of the DQ–JSQ chain with abandonment (Cao–He–Huang–Liu, §3, pp. 5–6,
(2)–(9)) on the augmented queue length `State n`. Lean indices are 0-based: `q.1 i` is the
paper's `Q_{i+1}`, the number of servers with at least `i + 1` customers.
* Arrivals form a Poisson process with **total** rate `lam`; under JSQ an arrival joins a server
  with the fewest customers; `ArrivesAt q i` says that this server has exactly `i` customers,
  and the new state is `up q i`.
* A server with exactly `i + 1` customers (there are `q.1 i − q.1 (i+1)` of them) loses a
  customer at rate `μ + θ i`: service at rate `μ` ((7)) and abandonment of each of its `i`
  waiting customers at rate `θ` ((8), paper rate `θ(i − 1)` for a server with `i` customers);
  the new state is `down q i`. -/
noncomputable def genAb (n : ℕ) (lam μ θ : ℝ) (f : State n → ℝ) (q : State n) : ℝ :=
  (∑' i : ℕ, (if ArrivesAt q i then lam else 0) * (f (up q i) - f q)) +
    ∑' i : ℕ, (μ + θ * (i : ℝ)) * ((q.1 i : ℝ) - (q.1 (i + 1) : ℝ)) * (f (down q i) - f q)

/-- `q := μ(ρ − 1)⁺/θ` of (18), p. 7. -/
noncomputable def qOf (ρ μ θ : ℝ) : ℝ :=
  μ * max (ρ - 1) 0 / θ

/-- `q̄ := ⌊q⌋ + 1` of (18), p. 7 (a natural number; `q ≥ 0`, so `Nat.floor` is the floor). -/
noncomputable def qBar (ρ μ θ : ℝ) : ℕ :=
  ⌊qOf ρ μ θ⌋₊ + 1

/-- `r := q − ⌊q⌋` of (18), p. 7. -/
noncomputable def rOf (ρ μ θ : ℝ) : ℝ :=
  qOf ρ μ θ - (⌊qOf ρ μ θ⌋₊ : ℝ)

/-- The invariant state `q*` of §4.2, p. 7, in the paper's 1-based indexing:
`q*_i = 1` for `1 ≤ i ≤ q̄`, `q*_{q̄+1} = r`, `q*_i = 0` for `i ≥ q̄ + 2`. The value at the
non-paper index `0` is `1` (the convention `Q̄_0 ≡ 1`). -/
noncomputable def qStar (ρ μ θ : ℝ) (i : ℕ) : ℝ :=
  if i ≤ qBar ρ μ θ then 1 else if i = qBar ρ μ θ + 1 then rOf ρ μ θ else 0

/-- The Bernoulli parameter `p := r(μ + θ q̄)/(ρμ)` of Theorem 4, p. 9. -/
noncomputable def pMix (ρ μ θ : ℝ) : ℝ :=
  rOf ρ μ θ * (μ + θ * (qBar ρ μ θ : ℝ)) / (ρ * μ)

/-- The fluid-scaled augmented queue length `Q̄ⁿ = Qⁿ/n` (p. 8) of a state, as a sequence in the
paper's 1-based indexing: index `i ≥ 1` is `Q_i/n` (Lean `q.1 (i − 1) / n`); index `0` is
`Q_0/n = 1`. -/
noncomputable def fluidScaled {n : ℕ} (q : State n) (i : ℕ) : ℝ :=
  if i = 0 then 1 else (q.1 (i - 1) : ℝ) / (n : ℝ)

/-- The metric `d(y, z) := Σ_{i ≥ 1} 2^{−i} (|y_i − z_i| ∧ 1)` on `ℝ^∞` (p. 8), for sequences in
the paper's 1-based indexing (index `0` is ignored). -/
noncomputable def dInf (y z : ℕ → ℝ) : ℝ :=
  ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) * min |y (i + 1) - z (i + 1)| 1

end PoolOrNot.Moderate


