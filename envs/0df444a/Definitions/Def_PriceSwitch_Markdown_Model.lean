-- Prove2me | Definitions.Def_PriceSwitch_Markdown_Model
-- name    : PriceSwitch_Markdown_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:52:06.243589+00:00
-- url     : https://prove2.me/theorems/aaa68885-9241-4fc2-aa96-4fca0c6a75de
-- title:
--   §2–§4.1 — two-price Poisson model, stopping class, and revenue value
-- statement:
--   Consider an inventory of $n$ units and a remaining horizon $t\ge 0$. Price $a$ has Poisson demand rate $\lambda_a$, while price $b$ has rate $\lambda_b$. Write $Q_m(j)$ for the upper tail $\Pr\{\operatorname{Poisson}(m)\ge j\}$ and $M_n(m)=\sum_{j=1}^{n}Q_m(j)$. The expected revenue from changing price at deterministic time $s\in[0,t]$ is
--
--   $$
--   J(n,t;s)=(a-b)M_n(\lambda_a s)+bM_n(\lambda_a s+\lambda_b(t-s)).
--   $$
--
--   The model also defines $G(n,t)=a\lambda_a-b\lambda_b-b(\lambda_a-\lambda_b)Q_{\lambda_b t}(n)$. The markdown case has $0<b<a$, $0<\lambda_a<\lambda_b$, and $a\lambda_a<b\lambda_b$; the markup case reverses the price, rate, and revenue-rate orders. The stochastic value is the supremum, over stopping times $\tau\in[0,t]$ adapted to the demand-count history with $N(\tau)\le n$ almost surely, of the expected revenue earned before and after the switch.
--
--   These definitions fix the notation used by Theorem 1 and its supporting statements. They also expose a terminal-revenue version of the stopping value, as the paper permits in its discussion of Lemma 1.
--
--   **Formalization Note** The sum of the independent Poisson counts is written through its $\operatorname{Poisson}(\lambda_a s+\lambda_b(t-s))$ law. The first demand process uses the referenced exponential-interarrival counting process. The stopping class uses the sigma algebra of all counts observed through each time. The payoff uses $\min(n,N(\tau))$ and truncated natural subtraction, which agree with the paper almost surely under the stock constraint. For nonnegative time and positive rates all Poisson means are nonnegative; the auxiliary tail maps a negative mean to zero. Under the theorem applications' continuous terminal revenue, admissible payoffs are bounded and measurable, so the real-valued supremum and expectation have their intended meaning. Positive prices and rates make explicit the convention used by the paper's cases.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), §2–§4.1, pp. 1375–1379, Eq. (2), https://doi.org/10.1287/mnsc.41.8.1371

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_ArrivalProcess

namespace PriceSwitch.Markdown

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

/-- `P(N ≥ j)` for a Poisson random variable `N` with mean `m ≥ 0` (Feng–Gallego 1995, p. 1377); a negative `m`
is read as `0`. For `j = 0` it is `1`. -/
noncomputable def poissonTail (m : ℝ) (j : ℕ) : ℝ :=
  1 - ∑ k ∈ Finset.range j, poissonPMFReal m.toNNReal k

/-- `E min(n, N) = ∑_{j=1}^{n} P(N ≥ j)` for `N` Poisson with mean `m` (p. 1377). -/
noncomputable def expMinPoisson (n : ℕ) (m : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, poissonTail m j

/-- `J(n, t; s)` (§3, p. 1377): the expected revenue from `n` items over time-to-go `t` when price `a` (Poisson
rate `la`) is charged over `(0, s]` and price `b` (rate `lb`) over `(s, t]`:
`(a − b) ∑_{j=1}^{n} P(N_a(s) ≥ j) + b ∑_{j=1}^{n} P(N_a(s) + N_b(t − s) ≥ j)`, the sum of the independent
counts being Poisson with mean `la s + lb (t − s)`. `switchRevenue a la b lb n t 0` is `J(n, t; 0)` (switch at
once) and `switchRevenue a la b lb n t t` is `J(n, t; t)` (never switch). -/
noncomputable def switchRevenue (a la b lb : ℝ) (n : ℕ) (t s : ℝ) : ℝ :=
  (a - b) * expMinPoisson n (la * s) + b * expMinPoisson n (la * s + lb * (t - s))

/-- `G(n, t) = r₁ − r₂ − p₂(λ₁ − λ₂)P(N₂(t) ≥ n)` (§4.1, p. 1379), with `r₁ = a·la`, `r₂ = b·lb`. -/
noncomputable def G (a la b lb : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  a * la - b * lb - b * (la - lb) * poissonTail (lb * t) n

/-- Case (i), the markdown problem (p. 1376): the second price is lower, `b < a`. Since `λ(·)` is strictly
decreasing, `la < lb`, and by the assumption "r_i > r_j whenever p_i < p_j" (p. 1375), `a·la < b·lb`.
Prices and rates are positive. -/
structure IsMarkdownPair (a la b lb : ℝ) : Prop where
  pos_price : 0 < b
  pos_rate : 0 < la
  price_lt : b < a
  rate_lt : la < lb
  revRate_lt : a * la < b * lb

/-- Case (ii), the markup problem (p. 1376): the second price is higher, `a < b`, so `lb < la` and
`b·lb < a·la`. Prices and rates are positive. -/
structure IsMarkupPair (a la b lb : ℝ) : Prop where
  pos_price : 0 < a
  pos_rate : 0 < lb
  price_lt : a < b
  rate_lt : lb < la
  revRate_lt : b * lb < a * la

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `σ{N(u) : 0 ≤ u ≤ s}` (p. 1378), the history of the counting process `N = countingProcess T` up to time
`s`. -/
noncomputable def history (T : ℕ → Ω → ℝ) (s : ℝ) : MeasurableSpace Ω :=
  ⨆ u ∈ Set.Icc (0 : ℝ) s, MeasurableSpace.comap (countingProcess T u) inferInstance

/-- The class `𝒯` (pp. 1377–1378): stopping times `τ` of the history of `N` with `0 ≤ τ ≤ t` and `N(τ) ≤ n`
almost surely. -/
structure IsAdmissible (P : Measure Ω) (T : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (τ : Ω → ℝ) : Prop where
  nonneg : ∀ ω, 0 ≤ τ ω
  le_horizon : ∀ ω, τ ω ≤ t
  stopping : ∀ s, MeasurableSet[history T s] {ω | τ ω ≤ s}
  stock : ∀ᵐ ω ∂P, countingProcess T (τ ω) ω ≤ n

/-- `sup_{τ ∈ 𝒯} E[a · min(n, N(τ)) + g(n − N(τ), t − τ)]` (pp. 1377–1379): the optimal expected revenue when
price `a` is charged until the stopping time `τ`, after which the terminal revenue `g(m, u)` is collected from
the `m` unsold items with time-to-go `u`. With `g = J(·, ·; 0)` this is `J(n, t)` of (2). -/
noncomputable def stopValue (P : Measure Ω) (T : ℕ → Ω → ℝ) (a : ℝ) (g : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ⨆ τ : {τ : Ω → ℝ // IsAdmissible P T n t τ},
    ∫ ω, (a * ((min n (countingProcess T (τ.1 ω) ω) : ℕ) : ℝ)
      + g (n - countingProcess T (τ.1 ω) ω) (t - τ.1 ω)) ∂P

/-- `J(n, t)` of (2) (p. 1377) for the two-price problem: start at `p₁`, switch once to `p₂`. The demand at
`p₁` is `countingProcess T` (the caller assumes `IsExpInterarrivals P lam₁ T`); `lam₁` enters only through
that hypothesis. -/
noncomputable def optRevenue (P : Measure Ω) (T : ℕ → Ω → ℝ) (p₁ lam₁ p₂ lam₂ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  stopValue P T p₁ (fun m u => switchRevenue p₁ lam₁ p₂ lam₂ m u 0) n t

end PriceSwitch.Markdown


