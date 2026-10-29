-- Prove2me | Definitions.Def_ChenChaoShiSALA_Regret_Observations
-- name    : ChenChaoShiSALA_Regret_Observations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:18:27.346993+00:00
-- url     : https://prove2.me/theorems/b039e31d-58a8-485a-a0ef-4f9a89d26b3c
-- title:
--   Algorithm 1, Step 2 — censored spline and two distinct stock selectors
-- statement:
--   Periods and observation blocks are zero-based. Period $t<N$ belongs to block $i=\lfloor t/(mL)\rfloor$, $j=\lfloor t/L\rfloor\bmod m$ and samples price $\tau_{i+1,j+1}$. Its observed sale is $\min(B,\lambda(\tau_{i+1,j+1})+\epsilon_t)$. For an input sales sequence $s$, the block mean $s_{ij}$ averages its $L$ entries. The empirical coefficient is exactly Algorithm 1's $\beta_i$, and $\widehat\lambda(p)=\sum_i\beta_iN_i^m(p)$. Residual $\eta_t$ equals the sale minus its own block mean, so residuals within a block share a random centering term. The surrogate profit is
--   $$\widehat Q(p,y)=p\widehat\lambda(p)-\frac{b+p}{N}\sum_{t<N}(\widehat\lambda(p)+\eta_t-y)^+-\frac hN\sum_{t<N}(y-\widehat\lambda(p)-\eta_t)^+.$$
--   The printed stock selector is the minimum residual whose unnormalized count $\sum_{t<N}1_{\eta_t\le\eta_j}$ is at least $q(p)$. Separately, the empirical stock selector compares that count divided by $N$ with $q(p)$. Only the latter supplies the least inventory optimizer. The former supplies the printed expected-lost-sales estimator $N^{-1}\sum_{t<N}(\eta_t-\widehat z(p))^+$ for Propositions 3–4. Finite minima are expressed by real infima; construction-domain and critical-ratio assumptions make their sets nonempty. The learner functions use only the supplied sales, endpoints, costs and horizon.
-- source:
--   Chen, Chao and Shi (2021), Nonparametric Learning Algorithms for Joint Pricing and Inventory Control with Lost Sales and Censored Demand, Mathematics of Operations Research, doi:10.1287/moor.2020.1084, supplied source.pdf, pp. 12–13, Algorithm 1, (9); pp. 16–17, (10)–(11)

import Definitions.Def_ChenChaoShiSALA_Regret_Parameters

open scoped BigOperators
noncomputable section

namespace ChenChaoShiSALA.Regret

/-- Periods and blocks are zero-based; knot/node indices remain one-based. -/
def explorationPrice (e : Market) (T t : ℕ) : ℝ :=
  (spline e T).node (t / (order T * blockLength T) + 1)
    (t / blockLength T % order T + 1)

def explorationSales (e : Market) (T : ℕ) (err : ℕ → ℝ) (t : ℕ) : ℝ :=
  InventoryBounds.sales (explorationLevel T) (e.demand (explorationPrice e T t) + err t)

/-- All subsequent statistical objects take sales, not errors or uncensored demands, as input. -/
def blockMean (T : ℕ) (sales : ℕ → ℝ) (i j : ℕ) : ℝ :=
  (∑ v ∈ Finset.range (blockLength T), sales ((i * order T + j) * blockLength T + v)) /
    (blockLength T : ℝ)

def empiricalCoefficient (e : Market) (T : ℕ) (sales : ℕ → ℝ) (i : ℕ) : ℝ :=
  (spline e T).alpha (i + 1) 1 * blockMean T sales i 0 +
    ∑ j ∈ Finset.range (order T - 1), ∑ v ∈ Finset.range (j + 2),
      (spline e T).alpha (i + 1) (j + 2) * blockMean T sales i v /
        ∏ r ∈ (Finset.range (j + 2)).erase v,
          ((spline e T).node (i + 1) (v + 1) - (spline e T).node (i + 1) (r + 1))

def estimatedDemand (e : Market) (T : ℕ) (sales : ℕ → ℝ) (p : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (order T + interiorKnots T),
    empiricalCoefficient e T sales i * (spline e T).basis (i + 1) p

def residual (T : ℕ) (sales : ℕ → ℝ) (t : ℕ) : ℝ :=
  sales t - blockMean T sales (t / (order T * blockLength T))
    (t / blockLength T % order T)

def empiricalProfit (e : Market) (T : ℕ) (sales : ℕ → ℝ) (p y : ℝ) : ℝ :=
  p * estimatedDemand e T sales p -
    (e.b + p) / (sampleSize T : ℝ) * (∑ t ∈ Finset.range (sampleSize T),
      max (estimatedDemand e T sales p + residual T sales t - y) 0) -
    e.h / (sampleSize T : ℝ) * (∑ t ∈ Finset.range (sampleSize T),
      max (y - estimatedDemand e T sales p - residual T sales t) 0)

/-- The literal UNNORMALIZED count printed on page 16, not the Step-3 quantile. -/
def printedStock (e : Market) (T : ℕ) (sales : ℕ → ℝ) (p : ℝ) : ℝ :=
  sInf {z : ℝ | ∃ j < sampleSize T, z = residual T sales j ∧
    e.quantileLevel p ≤ (∑ t ∈ Finset.range (sampleSize T),
      if residual T sales t ≤ residual T sales j then (1 : ℝ) else 0)}

/-- The normalized empirical quantile giving the least real inventory optimizer. -/
def empiricalStock (e : Market) (T : ℕ) (sales : ℕ → ℝ) (p : ℝ) : ℝ :=
  DataDrivenNV.LRS.saaQuantile (e.b + p) e.h
    (fun t : Fin (sampleSize T) => residual T sales t.val)

def estimatedLostSales (e : Market) (T : ℕ) (sales : ℕ → ℝ) (p : ℝ) : ℝ :=
  (∑ t ∈ Finset.range (sampleSize T), max (residual T sales t - printedStock e T sales p) 0) /
    (sampleSize T : ℝ)

end ChenChaoShiSALA.Regret


