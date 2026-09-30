-- Prove2me | Definitions.Def_InventoryControl_rqDiscrete
-- name    : InventoryControl_rqDiscrete
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-23T23:52:47.566918+00:00
-- url     : https://prove2.me/theorems/02b9da9b-66db-43f9-8177-e80d8d13a934
-- title:
--   Discrete lead-time demand, the $S$-policy cost $g(k)$, and the $(R,Q)$ cost $C(R,Q)$ of Sect. 6.1.1
-- statement:
--   The discrete-demand model of Axsäter, *Inventory Control*, Sects. 5.9.1 and 6.1.1: a
--   continuous review $(R,Q)$ policy with integral reorder point $R$ and batch quantity $Q$, a
--   holding cost $h$ per unit and time unit, a shortage cost $b_1$ per unit and time unit, an
--   ordering cost $A$ per batch, and an average demand $\mu$ per unit of time.
--
--   A `DiscreteDemand` is a probability distribution on the nonnegative integers with a finite
--   mean: `p j` is $\Pr[D(L) = j]$, the probability that the lead-time demand equals $j$. Its
--   `mean` is $\mu' = \sum_j j\,p_j$ and its `cdf k` is $\Pr[D(L) \le k]$ for an integer $k$,
--   which is $0$ for $k < 0$.
--
--   `sPolicyCost D h b1 k` is $g(k)$, the average holding and shortage cost rate of an
--   $(S-1,S)$ policy that keeps the inventory position at $k$ (Eq. 6.3, Eq. 6.20):
--
--   $$ g(k) \;=\; -b_1\,\mathbb{E}(IL) + (h + b_1)\,\mathbb{E}(IL^{+})
--      \;=\; -b_1\,(k - \mu') + (h + b_1)\sum_{j=1}^{k} j\,\Pr[D(L) = k - j], $$
--
--   using $IL = k - D(L)$ (Eq. 6.2) and the identity $x^{+} - x^{-} = x$ (Eq. 5.56).
--
--   `rqDiscreteCost D h b1 A μ R Q` is the total average cost rate of the $(R,Q)$ policy,
--   Eq. (6.4): since the inventory position is uniform on $\{R+1, \dots, R+Q\}$ (Proposition 5.1)
--   and each batch costs $A$,
--
--   $$ C(R,Q) \;=\; \frac{A\mu}{Q} + \frac{1}{Q}\sum_{k=R+1}^{R+Q} g(k). $$
--
--   `rqDiscreteReadyRate D R Q` is the ready rate $S_3 = \Pr[IL > 0]$ of the $(R,Q)$ policy,
--   Eq. (5.50) evaluated with the inventory level distribution (5.36):
--   $S_3(R) = \frac{1}{Q}\sum_{k=R+1}^{R+Q}\Pr[D(L) \le k - 1]$.
--
--   **Formalization Note** $R$ ranges over $\mathbb{Z}$ and $Q$ over $\mathbb{N}$; the divisions
--   by $Q$ are Lean's total division, so every theorem assumes $0 < Q$. Sums with an empty index
--   range are $0$, which is the book's reading of $\sum_{j=1}^{k}$ for $k \le 0$ and of
--   $\Pr[D(L) \le k]$ for $k < 0$. The mean $\mu'$ is a `tsum`, guarded by the summability field
--   of `DiscreteDemand`. The standing assumption that not all demands are multiples of an integer
--   larger than one, which the book needs for Proposition 5.1, is not part of this file: the cost
--   (6.4) takes the uniform inventory position as given, exactly as the book does.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, Sect. 5.9.1 pp. 84-85 (Eq. 5.57, 5.60), Sect. 6.1.1.1 pp. 107-108 (Eq. 6.2-6.5); the uniform inventory position is Proposition 5.1 p. 74

import Mathlib

namespace InventoryControl

/-- A lead-time demand distribution on the nonnegative integers with finite mean:
`p j = P(D(L) = j)`. Axsäter, *Inventory Control*, Sect. 6.1.1. -/
structure DiscreteDemand where
  p : ℕ → ℝ
  nonneg : ∀ j, 0 ≤ p j
  hasSum : HasSum p 1
  summable_mean : Summable (fun j : ℕ => (j : ℝ) * p j)

/-- The mean lead-time demand `μ' = μ L`. -/
noncomputable def DiscreteDemand.mean (D : DiscreteDemand) : ℝ := ∑' j : ℕ, (j : ℝ) * D.p j

/-- `P(D(L) ≤ k)` for an integer `k`; zero for `k < 0`. -/
noncomputable def DiscreteDemand.cdf (D : DiscreteDemand) (k : ℤ) : ℝ :=
  ∑ j ∈ Finset.Icc (0 : ℤ) k, D.p j.toNat

/-- `g(k)`: the average holding and shortage cost rate when the inventory position is kept at
`k`, Axsäter, *Inventory Control*, Eq. (6.3) and Eq. (6.20):
`g(k) = -b₁ (k - μ') + (h + b₁) ∑_{j=1}^{k} j P(D(L) = k - j)`. -/
noncomputable def sPolicyCost (D : DiscreteDemand) (h b1 : ℝ) (k : ℤ) : ℝ :=
  -b1 * ((k : ℝ) - D.mean) + (h + b1) * ∑ j ∈ Finset.Icc (1 : ℤ) k, (j : ℝ) * D.p (k - j).toNat

/-- `C(R, Q) = Aμ/Q + (1/Q) ∑_{k=R+1}^{R+Q} g(k)`, the total average cost rate of an `(R, Q)`
policy whose inventory position is uniform on `{R+1, …, R+Q}`. Axsäter, *Inventory Control*,
Eq. (6.4). -/
noncomputable def rqDiscreteCost (D : DiscreteDemand) (h b1 A μ : ℝ) (R : ℤ) (Q : ℕ) : ℝ :=
  A * μ / Q + (1 / (Q : ℝ)) * ∑ j ∈ Finset.range Q, sPolicyCost D h b1 (R + 1 + j)

/-- The ready rate `S₃ = P(IL > 0) = (1/Q) ∑_{k=R+1}^{R+Q} P(D(L) ≤ k - 1)` of an `(R, Q)`
policy, Axsäter, *Inventory Control*, Eq. (5.50) with Eq. (5.36). -/
noncomputable def rqDiscreteReadyRate (D : DiscreteDemand) (R : ℤ) (Q : ℕ) : ℝ :=
  (1 / (Q : ℝ)) * ∑ j ∈ Finset.range Q, D.cdf (R + j)

end InventoryControl


