-- Prove2me | Definitions.Def_QueueingFundamentals_MG1_embeddedChain
-- name    : QueueingFundamentals_MG1_embeddedChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T09:24:12.329513+00:00
-- url     : https://prove2.me/theorems/be555808-9478-4fdd-bb68-24ffbbb2dc51
-- title:
--   The M/G/1 departure-point chain, its stationary distributions and generating functions
-- statement:
--   Consider a single-server queue with Poisson arrivals at rate $\lambda > 0$ and independent service times $S$ with distribution $B$, a probability distribution on $[0,\infty)$. Let $X_n$ be the number of customers left behind by the $n$th departure. The number of arrivals during one service time is $i$ with probability
--
--   $$
--   k_i = \int_0^\infty \frac{e^{-\lambda t}(\lambda t)^i}{i!}\,dB(t), \qquad i = 0,1,2,\dots
--   $$
--
--   and $(X_n)$ is a Markov chain on $\{0,1,2,\dots\}$ with transition matrix
--
--   $$
--   p_{0j} = k_j, \qquad p_{ij} = \begin{cases} k_{j-i+1}, & j \ge i-1,\ 0, & j < i-1,\end{cases} \quad (i \ge 1).
--   $$
--
--   A **stationary distribution** of a transition matrix $P = (p_{ij})$ on $\{0,1,2,\dots\}$ is a sequence $\pi = (\pi_n)$ with $\pi_n \ge 0$, $\sum_n \pi_n = 1$ and $\pi P = \pi$, that is $\sum_i \pi_i p_{ij} = \pi_j$ for every $j$. The **generating function** of a real sequence $(a_i)$ is $\sum_{i \ge 0} a_i z^i$ for complex $z$; in particular $\Pi(z) = \sum_i \pi_i z^i$ and $K(z) = \sum_i k_i z^i$ for $|z| \le 1$. Finally $\mathrm E[S] = \int t\,dB(t)$, $\sigma_B^2 = \mathrm E[S^2] - \mathrm E^2[S]$, and the traffic intensity is $\rho = \lambda\,\mathrm E[S]$.
--
--   These are the objects of every statement about the M/G/1 departure-point chain in §5.1.
--
--   **Formalization Note** The arrival rate is `lam` (`λ` is a Lean keyword). `B` is any measure on `ℝ`; the theorems assume it is a probability measure with `B((-∞,0)) = 0`. `IsStationaryDist P π` states nonnegativity, `HasSum π 1` and `HasSum (fun i => π i * P i j) (π j)` for every `j`. `meanService` and `serviceVariance` are Bochner integrals, which are `0` for non-integrable integrands; every theorem that uses them assumes the integrability.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.225–227, Eqs. (5.9)–(5.11), (5.13), (5.15) and σ_B² in (5.6)

import Mathlib

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- `k_i = ∫_0^∞ e^{-λt}(λt)^i / i! dB(t)` (Eq. (5.9), p.226): the probability of `i` Poisson(`λ`)
arrivals during a service time with distribution `B`. The service distribution `B` is a measure on
`ℝ`; the theorems assume it is a probability measure concentrated on `[0, ∞)`. The arrival rate is
written `lam` because `λ` is a Lean keyword. -/
noncomputable def arrivalProb (lam : ℝ) (B : Measure ℝ) (i : ℕ) : ℝ :=
  ∫ t, Real.exp (-(lam * t)) * (lam * t) ^ i / (Nat.factorial i : ℝ) ∂B

/-- The transition matrix (5.10) (p.227) of the M/G/1 departure-point chain on `ℕ`:
row `0` is `(k_0, k_1, k_2, …)`, and for `i ≥ 1`, `p_{ij} = k_{j-i+1}` when `j ≥ i - 1` and `0`
otherwise. The index `j + 1 - i` is only used when `i ≤ j + 1`, so no natural-number subtraction
is truncated. -/
noncomputable def transitionMatrix (lam : ℝ) (B : Measure ℝ) (i j : ℕ) : ℝ :=
  if i = 0 then arrivalProb lam B j
  else if i ≤ j + 1 then arrivalProb lam B (j + 1 - i) else 0

/-- `π` is a stationary probability vector of the transition matrix `P` on `ℕ`: its entries are
nonnegative, sum to `1`, and satisfy `πP = π` (Eq. (5.11), p.227), i.e.
`∑_i π_i p_{ij} = π_j` for every `j`. -/
def IsStationaryDist (P : ℕ → ℕ → ℝ) (π : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ π n) ∧ HasSum π 1 ∧ ∀ j, HasSum (fun i => π i * P i j) (π j)

/-- The generating function `∑_{i ≥ 0} a_i z^i` of a real sequence `a` at a complex argument `z`
(Eq. (5.13), p.227, for `|z| ≤ 1`). `Π(z) = pgf π z` and `K(z) = pgf (arrivalProb lam B) z`. -/
noncomputable def pgf (a : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' i, (a i : ℂ) * z ^ i

/-- The mean service time `E[S] = ∫ t dB(t)`. -/
noncomputable def meanService (B : Measure ℝ) : ℝ :=
  ∫ t, t ∂B

/-- The service-time variance `σ_B² = E[S²] - E²[S]`. -/
noncomputable def serviceVariance (B : Measure ℝ) : ℝ :=
  (∫ t, t ^ 2 ∂B) - (meanService B) ^ 2

/-- The traffic intensity `ρ = λ E[S]` (Eq. (5.15), p.227; `ρ = λ/μ` with `μ = 1/E[S]`, p.219). -/
noncomputable def utilization (lam : ℝ) (B : Measure ℝ) : ℝ :=
  lam * meanService B

end QueueingFundamentals.MG1


