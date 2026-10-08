-- Prove2me | Definitions.Def_ServiceParts_StockLevels_Problems
-- name    : ServiceParts_StockLevels_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T07:14:45.147063+00:00
-- url     : https://prove2.me/theorems/29c6ddb6-a40f-4dd9-8038-fa3b0351a86c
-- title:
--   Problems 4 and 5 of Section 3.4: investment, total backorders, the Lagrangian cost f(s), the stock criterion, θ for zero stock, and the greedy fill-rate procedure
-- statement:
--   The optimization problems of Section 3.4 for $n$ item types (indexed by a finite set).
--
--   **Problem 4 (3.40).** Item $i$ has compound Poisson demand with backorder function $B_i$, mean lead-time demand $\mu_i$, and unit cost $c_i$. For a vector of stock levels $s = (s_i)$ the average investment in on-hand inventory and the total expected backorders are
--   $$\sum_i c_i\,[s_i - \mu_i + B_i(s_i)], \qquad \sum_i B_i(s_i).$$
--   For a Lagrange multiplier $\theta$ and a single item with unit cost $c$, the relaxed cost is
--   $$f(s) = (1 + \theta c)\,B(s) + \theta c\,s,$$
--   and the stock-level criterion set is $\{\, s : \sum_{x \le s} p(x \mid \mu) \ge 1/(1 + \theta c) \,\}$, whose least element is the book's $s^*(\theta)$. The multiplier at which $p(0 \mid \mu) = 1/(1 + \theta c)$ is
--   $$\theta_0 = \frac{1}{c}\Big(\frac{1}{p(0 \mid \mu)} - 1\Big).$$
--
--   **Problem 5 (3.41).** Item $i$ has simple Poisson demand with rate $\lambda_i$ and mean repair time $\bar\tau_i$, fill rate $F_i(s) = \sum_{x < s} p(x \mid \lambda_i\bar\tau_i)$, and unit cost $c_i$. The average expected system fill rate is
--   $$\sum_i \frac{\lambda_i}{\sum_j \lambda_j}\,F_i(s_i),$$
--   and the marginal gain per dollar of item $i$ at stock level $s_i$ is
--   $$\Delta_i(s_i) = \frac{\lambda_i}{\sum_j \lambda_j}\cdot\frac{F_i(s_i+1) - F_i(s_i)}{c_i}.$$
--   A **greedy run** is a sequence of stock vectors $s^{(0)}, s^{(1)}, \dots$ with $s^{(0)}_i = \lfloor \lambda_i\bar\tau_i \rfloor$ for every $i$, where $s^{(k+1)}$ is obtained from $s^{(k)}$ by raising by one the stock level of an item $i^*$ that maximizes $\Delta_i(s^{(k)}_i)$ (ties broken arbitrarily).
--
--   **Formalization Note** The greedy procedure is a predicate on sequences, so every tie-breaking rule is covered.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 60-61, 63-65, Section 3.4.2 (Problem 4, Eq. (3.40), f(s), s*(θ), C(θ), θmax) and Section 3.4.3 (Problem 5, Eq. (3.41), Δ_i(s_i), greedy procedure)

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand

namespace ServiceParts.StockLevels

/-! Problem 4 (3.40): minimize expected backorders subject to an investment budget. -/

/-- Average investment in on-hand inventory of a vector of stock levels,
`Σ_i c_i [s_i - µ_i + B_i(s_i)]` (Muckstadt 2005, p. 60, (3.40); `C(θ)` of p. 61 is this
quantity at `s = s*(θ)`). -/
noncomputable def totalInvestment {ι : Type*} [Fintype ι] (d : ι → CompoundPoissonDemand)
    (c : ι → ℝ) (s : ι → ℕ) : ℝ :=
  ∑ i, c i * ((s i : ℝ) - (d i).mu + (d i).backorders (s i))

/-- Total expected backorders `Σ_i B_i(s_i)`, the objective of Problem 4 (3.40). -/
noncomputable def totalBackorders {ι : Type*} [Fintype ι] (d : ι → CompoundPoissonDemand)
    (s : ι → ℕ) : ℝ :=
  ∑ i, (d i).backorders (s i)

/-- The single-item Lagrangian cost `f(s) = (1 + θc) B(s) + θ c s` (Muckstadt 2005, p. 61). -/
noncomputable def relaxedCost (d : CompoundPoissonDemand) (c θ : ℝ) (s : ℕ) : ℝ :=
  (1 + θ * c) * d.backorders s + θ * c * s

/-- The stock levels meeting the criterion of p. 61, `Σ_{x ≤ s} p(x|µ) ≥ 1/(1 + θc)`;
the book's `s*(θ)` is the least element of this set. -/
def stockSet (d : CompoundPoissonDemand) (c θ : ℝ) : Set ℕ :=
  {s | 1 / (1 + θ * c) ≤ d.readyRate s}

/-- `θ` at which `p(0|µ) = 1/(1 + θc)`, namely `(1/c)(1/p(0|µ) - 1)` (Muckstadt 2005, p. 63). -/
noncomputable def thetaZero (d : CompoundPoissonDemand) (c : ℝ) : ℝ :=
  1 / c * (1 / d.pmf 0 - 1)

/-! Problem 5 (3.41): maximize the average fill rate under simple Poisson demand. -/

/-- Average expected system fill rate `Σ_i (λ_i / Σ_j λ_j) F_i(s_i)` with
`F_i(s) = Σ_{x < s} p(x|λ_i τ̄_i)` (Muckstadt 2005, p. 64, (3.41)). -/
noncomputable def avgFillRate {ι : Type*} [Fintype ι] (lam tbar : ι → ℝ) (s : ι → ℕ) : ℝ :=
  ∑ i, lam i / (∑ j, lam j) * poissonFillRate (lam i * tbar i) (s i)

/-- Marginal fill-rate gain per dollar
`Δ_i(s_i) = (λ_i / Σ_j λ_j) (F_i(s_i + 1) - F_i(s_i)) / c_i` (Muckstadt 2005, p. 65). -/
noncomputable def greedyRatio {ι : Type*} [Fintype ι] (lam tbar c : ι → ℝ) (i : ι) (si : ℕ) : ℝ :=
  lam i / (∑ j, lam j) *
    ((poissonFillRate (lam i * tbar i) (si + 1) - poissonFillRate (lam i * tbar i) si) / c i)

/-- A run of the greedy (marginal analysis) procedure of p. 65: start at
`s_i = ⌊λ_i τ̄_i⌋` and, at every step, increase by one unit the stock level of an item
`i*` maximizing `Δ_i(s_i)` (ties broken arbitrarily). `seq k` is the vector after `k` steps. -/
def IsGreedySeq {ι : Type*} [Fintype ι] [DecidableEq ι] (lam tbar c : ι → ℝ)
    (seq : ℕ → ι → ℕ) : Prop :=
  (∀ i, seq 0 i = ⌊lam i * tbar i⌋₊) ∧
    ∀ k, ∃ istar : ι,
      (∀ i, greedyRatio lam tbar c i (seq k i) ≤ greedyRatio lam tbar c istar (seq k istar)) ∧
      seq (k + 1) = Function.update (seq k) istar (seq k istar + 1)

end ServiceParts.StockLevels


