-- Prove2me | Definitions.Def_BesbesZeevi_Nonparametric_Algorithm
-- name    : BesbesZeevi_Nonparametric_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:29:47.621706+00:00
-- url     : https://prove2.me/theorems/26fc91ed-e346-49af-ad01-be7613b8053e
-- title:
--   Algorithm 1 $\pi(\tau,\kappa)$: revenue, $J^\pi_n$, regret $\mathcal R^\pi_n$, $u_n$ and the tuning $\tau_n\asymp n^{-1/4}$, $\kappa_n\asymp n^{1/4}$
-- statement:
--   This file defines the nonparametric learn-then-price policy of Besbes and Zeevi (Algorithm 1, pp. 9–10) in a market of size $n$, where the inventory is $nx$ and the demand function is $n\lambda$ (scaling (11)).
--
--   Let $N$ be a unit-rate Poisson process. Fix a positive integer $\kappa$ and $\tau\in(0,T]$, and put $\Delta=\tau/\kappa$. The test prices are the left endpoints of $\kappa$ equal subintervals of $[\underline p,\overline p]$:
--
--   $$
--   p_i=\underline p+(i-1)\frac{\overline p-\underline p}{\kappa},\qquad i=1,\dots,\kappa.
--   $$
--
--   1. **Learning.** Price $p_i$ is applied on $[(i-1)\Delta,i\Delta)$. By the time change (1), the requests up to the end of the $i$-th interval are $N(\Lambda_i)$, where $\Lambda_i=\sum_{j\le i}n\lambda(p_j)\Delta$. The estimates (A-1) are
--   $$
--   \hat\lambda(p_i)=\frac{N(\Lambda_i)-N(\Lambda_{i-1})}{n\Delta}.
--   $$
--   2. **Optimization.** Set $\hat p^u=\arg\max_i p_i\hat\lambda(p_i)$, $\hat p^c=\arg\min_i|\hat\lambda(p_i)-x/T|$ and $\hat p=\max\{\hat p^c,\hat p^u\}$, as in (9)–(10). Ties go to the smallest index.
--   3. **Pricing.** $\hat p$ is applied on $(\tau,T]$. The uncapped requests are $Y^{(L)}_n=N(\Lambda_\kappa)$ and $Y_n=N(\Lambda_\kappa+n\lambda(\hat p)(T-\tau))$.
--
--   The inventory is $\lfloor nx\rfloor$ units. Once it runs out the policy posts $p_\infty$, so the units sold by intensity $\Lambda$ are $\min\{N(\Lambda),\lfloor nx\rfloor\}$. The revenue is
--
--   $$
--   \sum_{i=1}^{\kappa}p_i\big(\min\{N(\Lambda_i),\lfloor nx\rfloor\}-\min\{N(\Lambda_{i-1}),\lfloor nx\rfloor\}\big)+\hat p\big(\min\{Y_n,\lfloor nx\rfloor\}-\min\{Y^{(L)}_n,\lfloor nx\rfloor\}\big).
--   $$
--
--   Its expectation is $J^\pi_n(x,T;\lambda)$. The regret is $\mathcal R^\pi_n=1-J^\pi_n/J^D_n$. The analysis uses $u_n=(\log n)^{1/2}\max\{1/\kappa_n,(n\Delta_n)^{-1/2}\}$, from (A-3).
--
--   The tuning of Proposition 1 is $\tau_n\asymp n^{-1/4}$, $\kappa_n\asymp n^{1/4}$. Here it means: there are constants $0<c\le c'$ such that, for every $n\ge1$, $c\,n^{-1/4}\le\tau_n\le c'n^{-1/4}$, $0<\tau_n\le T$, $\kappa_n\ge1$ and $c\,n^{1/4}\le\kappa_n\le c'n^{1/4}$.
--
--   **Formalization Note** $N$ is a platform `IsPoissonProcess N 1` on a probability space $(\Omega,\mathbb P)$. Indices are 0-based in Lean. The estimate $\hat p$ is computed from the uncapped counts. This is harmless: after a stock-out during learning, every later capped increment is $0$, so the price applied afterwards earns nothing, exactly as when the paper's algorithm STOPs. The revenue takes finitely many values determined by finitely many values of $N$, and it is bounded by $\overline p\lfloor nx\rfloor$, so its expectation is a genuine (integrable) Bochner integral. The inventory $x_n=nx$ of (11) becomes $\lfloor nx\rfloor$ units, which equals $nx$ when $nx$ is an integer.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), pp. 7-10 (PDF 9-12), eqs. (1), (4), (6), Algorithm 1, (9), (10); p. 12 (PDF 14), (11), Proposition 1; pp. 28-29 (PDF 30-31), (A-1), (A-3)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_BesbesZeevi_Nonparametric_Model

namespace BesbesZeevi.Nonparametric

open MeasureTheory

/-- The grid of Algorithm 1, Step 1(b) (p. 10): the left endpoints of `κ` equal intervals of
`[p̲, p̄]`. The index is 0-based: `gridPrice P κ j = p̲ + j (p̄ - p̲)/κ` is the paper's `p_{j+1}`,
`j = 0, …, κ - 1`. -/
noncomputable def gridPrice (P : PriceSet) (κ : ℕ) (j : ℕ) : ℝ :=
  P.pl + (j : ℝ) * (P.pu - P.pl) / (κ : ℝ)

/-- Cumulative demand intensity of the learning phase in the market of size `n` (demand `n λ`):
`Λ_j = ∑_{i < j} n λ(p_{i+1}) Δ` with `Δ = τ/κ`, the intensity accumulated by the end of the
`j`-th test interval (0-based; `Λ_0 = 0`, `Λ_κ = X^{(L)}_n`, p. 28). -/
noncomputable def learnIntensity (P : PriceSet) (lam : ℝ → ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ)
    (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, (n : ℝ) * lam (gridPrice P κ i) * (τ / (κ : ℝ))

/-- The demand estimate (A-1) (p. 28) at the grid price `p_{j+1}`:
`λ̂(p_{j+1}) = [N(Λ_{j+1}) - N(Λ_j)] / (n Δ)`, the number of requests during the `(j+1)`-th test
interval normalized by `n Δ`, for a path of the unit-rate Poisson process `N`. -/
noncomputable def demandEstimate (P : PriceSet) (lam : ℝ → ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ)
    {Ω : Type*} (N : ℝ → Ω → ℕ) (j : ℕ) (ω : Ω) : ℝ :=
  (((N (learnIntensity P lam n τ κ (j + 1)) ω : ℕ) : ℝ)
      - ((N (learnIntensity P lam n τ κ j) ω : ℕ) : ℝ)) / ((n : ℝ) * (τ / (κ : ℝ)))

open Classical in
/-- Tie-breaking rule for the grid argmax of (9): the smallest index `j < κ` at which `f`
attains its maximum over `{0, …, κ - 1}` (`0` if `κ = 0`). -/
noncomputable def firstArgmax (κ : ℕ) (f : ℕ → ℝ) : ℕ :=
  if h : ∃ j, j < κ ∧ ∀ k, k < κ → f k ≤ f j then Nat.find h else 0

/-- `p̂^u = argmax_{1 ≤ i ≤ κ} p_i λ̂(p_i)` of (9), ties broken by the smallest index. -/
noncomputable def phatU (P : PriceSet) (lam : ℝ → ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ)
    {Ω : Type*} (N : ℝ → Ω → ℕ) (ω : Ω) : ℝ :=
  gridPrice P κ
    (firstArgmax κ (fun j => gridPrice P κ j * demandEstimate P lam n τ κ N j ω))

/-- `p̂^c = argmin_{1 ≤ i ≤ κ} |λ̂(p_i) - x/T|` of (9), ties broken by the smallest index. -/
noncomputable def phatC (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ)
    {Ω : Type*} (N : ℝ → Ω → ℕ) (ω : Ω) : ℝ :=
  gridPrice P κ
    (firstArgmax κ (fun j => -|demandEstimate P lam n τ κ N j ω - x / T|))

/-- `p̂ = max{p̂^c, p̂^u}` of (10), the price applied in the pricing phase. -/
noncomputable def phat (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ)
    {Ω : Type*} (N : ℝ → Ω → ℕ) (ω : Ω) : ℝ :=
  max (phatC P lam x T n τ κ N ω) (phatU P lam n τ κ N ω)

/-- The inventory of the market of size `n`, in units: `⌊n x⌋` (the paper's `x_n = n x`, (11);
sales are integer, so constraint (2) caps them at `⌊n x⌋`). -/
noncomputable def salesCap (n : ℕ) (x : ℝ) : ℕ :=
  ⌊(n : ℝ) * x⌋₊

/-- Cumulative demand intensity at the end of the horizon if the system never ran out:
`X^{(L)}_n + X^{(P)}_n = Λ_κ + n λ(p̂) (T - τ)` (p. 28). It depends on `ω` through `p̂`. -/
noncomputable def endIntensity (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ)
    {Ω : Type*} (N : ℝ → Ω → ℕ) (ω : Ω) : ℝ :=
  learnIntensity P lam n τ κ κ + (n : ℝ) * lam (phat P lam x T n τ κ N ω) * (T - τ)

/-- `Y^{(L)}_n = N(X^{(L)}_n)`, the requests of the learning phase if stock never ran out
(p. 28). -/
noncomputable def requestsLearn (P : PriceSet) (lam : ℝ → ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ)
    {Ω : Type*} (N : ℝ → Ω → ℕ) (ω : Ω) : ℕ :=
  N (learnIntensity P lam n τ κ κ) ω

/-- `Y_n = N(X^{(L)}_n + X^{(P)}_n)`, the requests over the whole horizon if stock never ran out
(p. 28). -/
noncomputable def requestsTotal (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ)
    {Ω : Type*} (N : ℝ → Ω → ℕ) (ω : Ω) : ℕ :=
  N (endIntensity P lam x T n τ κ N ω) ω

/-- The revenue of Algorithm 1, `π(τ, κ)`, on one path of the unit-rate Poisson process `N`, in
the market of size `n` (inventory `⌊n x⌋`, demand `n λ`). By the time change (1) the cumulative
requests at intensity `Λ` are `N(Λ)`, and units sold are `min{N(Λ), ⌊n x⌋}` (after a stock-out the
algorithm posts `p_∞`, whose demand is `0`). The revenue is the price of each phase times the
units sold in it:
`∑_{j<κ} p_{j+1} (min{N(Λ_{j+1}), cap} - min{N(Λ_j), cap}) + p̂ (min{Y_n, cap} - min{Y^{(L)}_n, cap})`. -/
noncomputable def revenue (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ)
    {Ω : Type*} (N : ℝ → Ω → ℕ) (ω : Ω) : ℝ :=
  (∑ j ∈ Finset.range κ, gridPrice P κ j *
      (((min (N (learnIntensity P lam n τ κ (j + 1)) ω) (salesCap n x) : ℕ) : ℝ)
        - ((min (N (learnIntensity P lam n τ κ j) ω) (salesCap n x) : ℕ) : ℝ)))
  + phat P lam x T n τ κ N ω *
      (((min (requestsTotal P lam x T n τ κ N ω) (salesCap n x) : ℕ) : ℝ)
        - ((min (requestsLearn P lam n τ κ N ω) (salesCap n x) : ℕ) : ℝ))

/-- `J^π_n(x, T; λ)`: the expected revenue (4) of Algorithm 1 `π(τ, κ)` in the market of size
`n`, the expectation taken under the probability measure `ℙ` carrying `N`. -/
noncomputable def expectedRevenue (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (n : ℕ) (τ : ℝ)
    (κ : ℕ) {Ω : Type*} [MeasureSpace Ω] (N : ℝ → Ω → ℕ) : ℝ :=
  ∫ ω, revenue P lam x T n τ κ N ω

/-- The regret `R^π_n(x, T; λ) = 1 - J^π_n(x, T; λ) / J^D_n(x, T | λ)` (p. 12). -/
noncomputable def regret (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (n : ℕ) (τ : ℝ) (κ : ℕ)
    {Ω : Type*} [MeasureSpace Ω] (N : ℝ → Ω → ℕ) : ℝ :=
  1 - expectedRevenue P lam x T n τ κ N / JDn P lam x T n

/-- `u_n = (log n)^{1/2} max{1/κ_n, 1/(n Δ_n)^{1/2}}` with `Δ_n = τ_n/κ_n`, (A-3) (p. 29). -/
noncomputable def uSeq (n : ℕ) (τ : ℝ) (κ : ℕ) : ℝ :=
  Real.sqrt (Real.log n) * max (1 / (κ : ℝ)) (1 / Real.sqrt ((n : ℝ) * (τ / (κ : ℝ))))

/-- The tuning of Proposition 1 (p. 12): `τ_n ≍ n^{-1/4}` and `κ_n ≍ n^{1/4}`, with `κ_n` a
positive integer and `τ_n ∈ (0, T]` (Algorithm 1 requires `τ ∈ (0, T]`, p. 9). Here `≍` is
rendered with explicit constants `0 < c ≤ c'`, for every `n ≥ 1`. -/
structure Tuning (T c c' : ℝ) (τ : ℕ → ℝ) (κ : ℕ → ℕ) : Prop where
  c_pos : 0 < c
  c_le : c ≤ c'
  tau_pos : ∀ n : ℕ, 1 ≤ n → 0 < τ n
  tau_le : ∀ n : ℕ, 1 ≤ n → τ n ≤ T
  tau_lower : ∀ n : ℕ, 1 ≤ n → c * (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ τ n
  tau_upper : ∀ n : ℕ, 1 ≤ n → τ n ≤ c' * (n : ℝ) ^ (-(1 / 4 : ℝ))
  kappa_pos : ∀ n : ℕ, 1 ≤ n → 1 ≤ κ n
  kappa_lower : ∀ n : ℕ, 1 ≤ n → c * (n : ℝ) ^ (1 / 4 : ℝ) ≤ (κ n : ℝ)
  kappa_upper : ∀ n : ℕ, 1 ≤ n → (κ n : ℝ) ≤ c' * (n : ℝ) ^ (1 / 4 : ℝ)

end BesbesZeevi.Nonparametric


