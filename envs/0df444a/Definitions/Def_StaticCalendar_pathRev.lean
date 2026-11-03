-- Prove2me | Definitions.Def_StaticCalendar_pathRev
-- name    : StaticCalendar_pathRev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:04.198375+00:00
-- url     : https://prove2.me/theorems/e6522df2-3da2-4efe-9d40-d062adf39afc
-- title:
--   Sequential revenue under static substitution
-- statement:
--   This is the revenue of one sample run. Suppose the offers and demands of $k$ periods are $(S_t,Q^t)$ and the starting inventories are $c=(c_i)$. In each period, with remaining inventory $B$, each product $(i,j)\in S_t$ sells $\min\{B_i,Q^t_{ij}\}$ and earns $p_j$ per unit. Item $i$'s inventory then drops by $\min\{B_i,\sum_{j:(i,j)\in S_t}Q^t_{ij}\}$. Under the model at most one summand is positive, so this is the amount sold.
--
--   This is **static substitution**: a product of a stocked-out item stays in the assortment, its demand is lost, and no other product's demand changes. Inventories may be fractional, and an item with $0.5$ units left sells $0.5$ of a unit demand.
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, static substitution, p.10; R_t(i,j) = min{B_i,Q} and B_t(i) = B_{t-1}(i) - R_t(i,j), p.ec9

import Mathlib
import Definitions.Def_StaticCalendar_DemandModel

namespace StaticCalendar

/-- The prices at which item `i` appears in assortment `S`. -/
def pricesOf {n m : ℕ} (S : Assortment n m) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => (i, j) ∈ S)

/-- The quantity of item `i` demanded in a period with offer `S` and demand `Q`, the sum of
`Q (i,j)` over the products of `i` in `S`. By `DemandModel.one_price` at most one summand is positive. -/
def itemDemand {n m : ℕ} (i : Fin n) (w : Assortment n m × Demand n m) : ℝ :=
  ∑ j ∈ pricesOf w.1 i, w.2 (i, j)

/-- Revenue of one period under static substitution with remaining inventories `c`: each product
`(i,j)` of the offered assortment sells `R(i,j) = min{cᵢ, Q}`, arXiv:1811.01077v5, p.ec9. -/
def stepRev {n m : ℕ} (p : Fin m → ℝ) (c : Fin n → ℝ) (w : Assortment n m × Demand n m) : ℝ :=
  ∑ i, ∑ j ∈ pricesOf w.1 i, p j * min (c i) (w.2 (i, j))

/-- Remaining inventories after one period: `Bₜ(i) = Bₜ₋₁(i) − Rₜ(i,j)`, p.ec9, which is
`max{0, c − Q}` (p.ec12). -/
def stepInv {n m : ℕ} (c : Fin n → ℝ) (w : Assortment n m × Demand n m) : Fin n → ℝ :=
  fun i => c i - min (c i) (itemDemand i w)

/-- The revenue of a run of `k` periods under static substitution, from starting inventories `c`,
when the offers and demands of the periods are `ω t = (Sₜ, Qₜ)`. arXiv:1811.01077v5, p.10 (model 1)
and p.ec9.

**Formalization Note.** A product of a stocked-out item stays offered and its demand is lost; the
other items' demands are unaffected. An item with `0.5` units left sells `0.5` of a unit demand. -/
def pathRev {n m : ℕ} (p : Fin m → ℝ) :
    (k : ℕ) → (Fin n → ℝ) → (Fin k → Assortment n m × Demand n m) → ℝ
  | 0, _, _ => 0
  | k + 1, c, ω => stepRev p c (ω 0) + pathRev p k (stepInv c (ω 0)) (Fin.tail ω)

end StaticCalendar


