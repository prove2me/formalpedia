-- Prove2me | Definitions.Def_SampleMechDesign_Supplement_secondPriceProfit
-- name    : SampleMechDesign_Supplement_secondPriceProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:44:49.603806+00:00
-- url     : https://prove2.me/theorems/9562cae3-9073-5e01-a136-4ea2944dadb2
-- title:
--   Section 3.4.3 — second price item auctions with anonymous and non-anonymous reserves
-- statement:
--   The buyers are additive and bid their values on each item. Under **non-anonymous reserves** there is a reserve $p_j(e_i)\ge0$ for each item $i$ and buyer $j$; under **anonymous reserves** $p_1(e_i)=\dots=p_n(e_i)$. For each item $i$, a highest bidder $j$ wins the item if her bid is above $p_j(e_i)$, and she pays
--   $$
--   \max\Big(\text{second highest bid on } i,\ p_j(e_i)\Big).
--   $$
--   The profit is the sum of the payments minus the cost $c$ of the resulting allocation.
--
--   **Formalization Note** "Above" is strict. The second highest bid is the highest bid of the other buyers; with a single buyer the price is the reserve. Ties among highest bidders are broken by a tie-breaking rule that may depend on the valuation vector and the item.
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Section 3.4.3, p.13 (PDF p.13)

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_Alloc

namespace SampleMechDesign.Supplement

open Finset

/-- **Second price item auctions with reserves.** Balcan, Sandholm, Vitercik,
arXiv:1705.00243v6, Section 3.4.3, p.13.

The buyers are additive and bid their values `v j i` on each item `i`. Under non-anonymous
reserves there is a reserve `r j i` for each item and buyer. For each item `i`, a highest bidder
`j` (chosen by the tie-breaking rule `tb` among the highest bidders `spaTop v i`) wins the item if
her bid is above `r j i`, and she pays the maximum of the second highest bid and `r j i`. Under
anonymous reserves, `r 1 i = ⋯ = r n i`.

`secondPriceProfit tb c r v` is the payments collected minus the cost of the resulting
allocation. `secondPriceClass` and `anonSecondPriceClass` are the classes with non-anonymous and
anonymous nonnegative reserves.

**Formalization Note.**
* "Above" is strict: the winner gets the item iff `r j i < v j i`.
* "The second highest bid" is the highest bid of the other buyers. With a single buyer there is
  none and the price is the reserve; the price is computed as the maximum of the finite set
  `{r j i} ∪ {v j' i : j' ≠ j}`.
* Ties among highest bidders are broken by `tb`, which may depend on the valuation vector and the
  item. -/
noncomputable def spaTop {n m : ℕ} (v : AVal n m) (i : Fin m) : Finset (Fin n) :=
  univ.filter fun j => ∀ j', v j' i ≤ v j i

/-- The highest bidder chosen for item `i`. -/
noncomputable def spaWinner {n m : ℕ} (tb : AVal n m × Fin m → Finset (Fin n) → Fin n)
    (v : AVal n m) (i : Fin m) : Fin n :=
  tb (v, i) (spaTop v i)

/-- The price paid by the winner `j` of item `i`: the maximum of her reserve and the other
bids. -/
noncomputable def spaPrice {n m : ℕ} (r : Fin n → Fin m → ℝ) (v : AVal n m) (j : Fin n)
    (i : Fin m) : ℝ :=
  (insert (r j i) ((univ.erase j).image fun j' => v j' i)).max' (insert_nonempty _ _)

/-- The bundles won. -/
noncomputable def spaAllocation {n m : ℕ} (tb : AVal n m × Fin m → Finset (Fin n) → Fin n)
    (r : Fin n → Fin m → ℝ) (v : AVal n m) : Bundles n m :=
  fun j => univ.filter fun i => spaWinner tb v i = j ∧ r j i < v j i

/-- Profit of the second price item auction with reserves `r` on `v`. -/
noncomputable def secondPriceProfit {n m : ℕ} (tb : AVal n m × Fin m → Finset (Fin n) → Fin n)
    (c : Bundles n m → ℝ) (r : Fin n → Fin m → ℝ) (v : AVal n m) : ℝ :=
  ∑ i, (if r (spaWinner tb v i) i < v (spaWinner tb v i) i then
      spaPrice r v (spaWinner tb v i) i else 0) - c (spaAllocation tb r v)

/-- Second price item auctions with non-anonymous nonnegative reserves. -/
def secondPriceClass {n m : ℕ} (tb : AVal n m × Fin m → Finset (Fin n) → Fin n)
    (c : Bundles n m → ℝ) : Set (AVal n m → ℝ) :=
  {f | ∃ r : Fin n → Fin m → ℝ, (∀ j i, 0 ≤ r j i) ∧ f = secondPriceProfit tb c r}

/-- Second price item auctions with anonymous nonnegative reserves. -/
def anonSecondPriceClass {n m : ℕ} (tb : AVal n m × Fin m → Finset (Fin n) → Fin n)
    (c : Bundles n m → ℝ) : Set (AVal n m → ℝ) :=
  {f | ∃ r : Fin m → ℝ, (∀ i, 0 ≤ r i) ∧ f = secondPriceProfit tb c (fun _ => r)}

end SampleMechDesign.Supplement


