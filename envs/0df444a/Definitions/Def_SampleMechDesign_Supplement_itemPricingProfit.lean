-- Prove2me | Definitions.Def_SampleMechDesign_Supplement_itemPricingProfit
-- name    : SampleMechDesign_Supplement_itemPricingProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:44:23.560594+00:00
-- url     : https://prove2.me/theorems/efc3e7b1-4675-4be4-84a0-e64562f48dea
-- title:
--   Section 3.4.2 — item-pricing mechanisms with a fixed arrival order
-- statement:
--   There is one unit of each item. A **non-anonymous item-pricing mechanism** is a price $p_j(e_i)\ge0$ for each buyer $j$ and item $i$; an **anonymous** one charges every buyer the same price $p(e_i)$. The buyers arrive in a fixed, arbitrary order. Each buyer $j$ in turn buys, among the items still unsold, a bundle $q$ that maximizes his utility
--   $$
--   v_j(q)-\sum_{i\in q}p_j(e_i),
--   $$
--   ties being broken by a tie-breaking rule. If $q_1,\dots,q_n$ are the bundles bought, the profit is
--   $$
--   \mathrm{profit}_p(v)=\sum_{j=1}^n\sum_{i\in q_j}p_j(e_i)-c(q_1,\dots,q_n).
--   $$
--   The classes $\mathcal M$ and $\mathcal M'$ of anonymous and non-anonymous item-pricing mechanisms are the sets of these profit functions on additive valuation vectors.
--
--   **Formalization Note** The arrival order is a permutation `ord` of the buyers, a parameter of the definition. The tie-breaking rule may depend on the valuation vector and the buyer. Prices are nonnegative.
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Section 3.4.2, p.13 (PDF p.13); Example 3.4, p.8

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_Alloc

namespace SampleMechDesign.Supplement

open Finset

/-- **Item-pricing mechanisms.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6,
Section 3.4.2, p.13 (also Example 3.4, p.8).

There is one unit of each item. A non-anonymous mechanism is a price `p j i` for every buyer `j`
and item `i` (an anonymous one has `p j i = p' i`). The buyers arrive in a fixed, arbitrary order
`ord 0, ord 1, …, ord (n-1)`; each buyer `j` in turn buys, among the items `R` still unsold, a bundle
`q ⊆ R` maximizing his utility `v_j(q) − ∑_{i ∈ q} p_j(e_i)`. `ipDemand v p j R` is that set of
utility-maximizing bundles and the tie-breaking rule `tb` picks one of them. `ipAllocation` is the
resulting profile of bundles and

`ipProfit ord tb c p v = ∑_j ∑_{i ∈ q_j} p_j(e_i) − c(q_1, …, q_n)`

is the profit: the prices paid minus the cost of the allocation.

`itemPricingClass` and `anonItemPricingClass` are the classes of non-anonymous and anonymous
item-pricing mechanisms, as functions on additive valuation vectors, with nonnegative prices.

**Formalization Note.**
* The arrival order is the parameter `ord : Fin n ≃ Fin n`; the paper fixes an arbitrary one.
* Ties among utility-maximizing bundles are broken by `tb`, which may depend on the valuation
  vector and the buyer (the paper does not say how ties are broken).
* Profit is the prices collected minus the production cost `c` of the final allocation.
* Prices are nonnegative. -/
noncomputable def ipDemand {n m : ℕ} (v : BVal n m) (p : Fin n → Fin m → ℝ) (j : Fin n)
    (R : Finset (Fin m)) : Finset (Finset (Fin m)) :=
  R.powerset.filter fun q =>
    ∀ q' ∈ R.powerset, v j q' - ∑ i ∈ q', p j i ≤ v j q - ∑ i ∈ q, p j i

/-- The state after the first `k` arrivals: the unsold items and the bundles bought so far. -/
noncomputable def ipState {n m : ℕ} (ord : Fin n ≃ Fin n)
    (tb : BVal n m × Fin n → Finset (Finset (Fin m)) → Finset (Fin m)) (v : BVal n m)
    (p : Fin n → Fin m → ℝ) : ℕ → Finset (Fin m) × Bundles n m
  | 0 => (univ, fun _ => ∅)
  | k + 1 =>
    if h : k < n then
      let st := ipState ord tb v p k
      let j := ord ⟨k, h⟩
      let q := tb (v, j) (ipDemand v p j st.1)
      (st.1 \ q, Function.update st.2 j q)
    else ipState ord tb v p k

/-- The bundles bought once all `n` buyers have arrived. -/
noncomputable def ipAllocation {n m : ℕ} (ord : Fin n ≃ Fin n)
    (tb : BVal n m × Fin n → Finset (Finset (Fin m)) → Finset (Fin m)) (v : BVal n m)
    (p : Fin n → Fin m → ℝ) : Bundles n m :=
  (ipState ord tb v p n).2

/-- Profit of the item-pricing mechanism with prices `p` on the valuation vector `v`. -/
noncomputable def ipProfit {n m : ℕ} (ord : Fin n ≃ Fin n)
    (tb : BVal n m × Fin n → Finset (Finset (Fin m)) → Finset (Fin m)) (c : Bundles n m → ℝ)
    (p : Fin n → Fin m → ℝ) (v : BVal n m) : ℝ :=
  ∑ j, ∑ i ∈ ipAllocation ord tb v p j, p j i - c (ipAllocation ord tb v p)

/-- The class of non-anonymous item-pricing mechanisms (nonnegative prices) over additive
buyers. -/
def itemPricingClass {n m : ℕ} (ord : Fin n ≃ Fin n)
    (tb : BVal n m × Fin n → Finset (Finset (Fin m)) → Finset (Fin m)) (c : Bundles n m → ℝ) :
    Set (AVal n m → ℝ) :=
  {f | ∃ p : Fin n → Fin m → ℝ, (∀ j i, 0 ≤ p j i) ∧
    f = fun v => ipProfit ord tb c p (additiveVal v)}

/-- The class of anonymous item-pricing mechanisms (one nonnegative price per item) over
additive buyers. -/
def anonItemPricingClass {n m : ℕ} (ord : Fin n ≃ Fin n)
    (tb : BVal n m × Fin n → Finset (Finset (Fin m)) → Finset (Fin m)) (c : Bundles n m → ℝ) :
    Set (AVal n m → ℝ) :=
  {f | ∃ p : Fin m → ℝ, (∀ i, 0 ≤ p i) ∧
    f = fun v => ipProfit ord tb c (fun _ => p) (additiveVal v)}

end SampleMechDesign.Supplement


