-- Prove2me | Definitions.Def_ChenChaoShiSALA_Regret_Algorithm
-- name    : ChenChaoShiSALA_Regret_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:19:07.267+00:00
-- url     : https://prove2.me/theorems/30e0ecbd-c573-4ea7-9914-6556c250f1fc
-- title:
--   Algorithm 1 — actual optimizer, carryover path and cumulative regret
-- statement:
--   At price $p$, the least inventory maximizer of the sample-average objective is $\widehat\lambda(p)$ plus the normalized empirical residual quantile. Choose the least grid price $\widehat p$ for which this inventory attains a profit at least as large as $\widehat Q(q,y)$ for every grid price $q$ and every real $y$; let $\widehat y$ be its inventory target. This is actual optimization over all real inventory levels, not the erroneous unnormalized-count stock selector. Grid and quantile infima are minima on the intended nonempty finite sample domain.
--
--   Starting with $x_1=0$, exploration period $t<N$ uses its sampling price and $y_t=B$ exactly. Exploitation uses $p_t=\widehat p$ and $y_t=\max(x_t,\widehat y)$. The next inventory is $(y_t-\lambda(p_t)-\epsilon_t)^+$. Neither negative demands nor residual carryover are removed. The whole finite path is computed by recursion, with no success or feasibility event assumed. With zero-based indices, exploitation starts at index $N$, corresponding to printed period $N+1$. The two expectations are
--   $$R(T)=TQ(p^*,y^*)-\mathbb E\sum_{t<T}Q(p_t,y_t),\qquad C(T)=\mathbb E\sum_{t=N}^{T-1}|Q(\widehat p,\widehat y)-Q(\widehat p,y_t)|.$$
--   The observation array used in recommendations consists solely of exploration sales. Once exploitation starts all of these observations are in the past. These functions implement the literal algorithm even on negative-demand paths where its exploration target may violate economic replenishment feasibility.
-- source:
--   Chen, Chao and Shi (2021), Nonparametric Learning Algorithms for Joint Pricing and Inventory Control with Lost Sales and Censored Demand, Mathematics of Operations Research, doi:10.1287/moor.2020.1084, supplied source.pdf, pp. 7–9, dynamics and (3); pp. 12–13, Algorithm 1; p. 18, Proposition 5

import Definitions.Def_ChenChaoShiSALA_Regret_Observations

open MeasureTheory
open scoped BigOperators
noncomputable section

namespace ChenChaoShiSALA.Regret

def targetAtPrice (e : Market) (T : ℕ) (sales : ℕ → ℝ) (p : ℝ) : ℝ :=
  estimatedDemand e T sales p + empiricalStock e T sales p

/-- The least price attaining the maximum over the sparse grid and ALL real inventories. -/
def recommendedPrice (e : Market) (T : ℕ) (sales : ℕ → ℝ) : ℝ :=
  sInf {p : ℝ | p ∈ priceGrid e T ∧
    ∀ q ∈ priceGrid e T, ∀ y : ℝ,
      empiricalProfit e T sales q y ≤ empiricalProfit e T sales p (targetAtPrice e T sales p)}

def recommendedInventory (e : Market) (T : ℕ) (sales : ℕ → ℝ) : ℝ :=
  targetAtPrice e T sales (recommendedPrice e T sales)

/-- x_1=0; at zero-based time t the recursion computes x_(t+2). -/
def inventory (e : Market) (T : ℕ) (err : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 =>
    let sales := explorationSales e T err
    let p := if t < sampleSize T then explorationPrice e T t else recommendedPrice e T sales
    let y := if t < sampleSize T then explorationLevel T else
      max (inventory e T err t) (recommendedInventory e T sales)
    InventoryBounds.lostNext y (e.demand p + err t)

def implementedPrice (e : Market) (T : ℕ) (err : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t < sampleSize T then explorationPrice e T t
  else recommendedPrice e T (explorationSales e T err)

def implementedInventory (e : Market) (T : ℕ) (err : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t < sampleSize T then explorationLevel T
  else max (inventory e T err t) (recommendedInventory e T (explorationSales e T err))

def regret {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (e : Market) (T : ℕ) (err : ℕ → Ω → ℝ) : ℝ :=
  T * e.Q e.pStar e.yStar - ∫ ω, ∑ t ∈ Finset.range T,
    e.Q (implementedPrice e T (fun s => err s ω) t)
      (implementedInventory e T (fun s => err s ω) t) ∂μ

def carryoverCost {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (e : Market) (T : ℕ) (err : ℕ → Ω → ℝ) : ℝ :=
  ∫ ω, ∑ t ∈ Finset.Ico (sampleSize T) T,
    |e.Q (recommendedPrice e T (explorationSales e T (fun s => err s ω)))
        (recommendedInventory e T (explorationSales e T (fun s => err s ω))) -
      e.Q (recommendedPrice e T (explorationSales e T (fun s => err s ω)))
        (implementedInventory e T (fun s => err s ω) t)| ∂μ

end ChenChaoShiSALA.Regret


