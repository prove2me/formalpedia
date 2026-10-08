-- Prove2me | Definitions.Def_ShapleyScarf_TopTrading_Market
-- name    : ShapleyScarf_TopTrading_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:50.071857+00:00
-- url     : https://prove2.me/theorems/2e0dffa6-2beb-4f2f-b806-396afd218822
-- title:
--   Section 2, pp. 106-107 and Section 6, p. 114 — core allocations and competitive allocations of the housing market
-- statement:
--   **The housing market.** There are finitely many traders, collected in a set $N$; each trader brings one indivisible good to the market, and "item $j$" is the good brought by trader $j$. Preferences are described by a real matrix $A = (a_{ij})_{i,j\in N}$: $a_{ij} > a_{ik}$ means that trader $i$ prefers item $j$ to item $k$, and $a_{ij} = a_{ik}$ that he is indifferent. Only the ordinal comparisons matter, and ties are allowed. A (permutation) **allocation** is a bijection $\sigma : N \to N$: trader $i$ ends up holding item $\sigma(i)$.
--
--   **Core allocation.** For a coalition $S \subseteq N$, an **$S$-permutation** is a reshuffling of the items of $S$ among the members of $S$: a map $\tau$ sending $S$ injectively (hence bijectively) into $S$. The allocation $\sigma$ is a **core allocation** if no nonempty coalition $S$ could have done better for all of its members, i.e. there is no nonempty $S$ and $S$-permutation $\tau$ with
--   $$a_{i\,\tau(i)} > a_{i\,\sigma(i)}\qquad\text{for every } i\in S.$$
--
--   **Competitive allocation.** A price vector $\mathrm{price} : N \to \mathbb R$ assigns a price to each item. The allocation $\sigma$ is **competitive** at these prices if every trader $i$, selling his own item for $\mathrm{price}(i)$, can afford the item he receives, and no affordable item is better for him:
--   $$\mathrm{price}(\sigma(i)) \le \mathrm{price}(i),\qquad \mathrm{price}(k) \le \mathrm{price}(i) \;\Longrightarrow\; a_{ik} \le a_{i\,\sigma(i)}\quad\text{for all } k\in N.$$
--   Supply equals demand because $\sigma$ is a bijection.
--
--   These two notions are the solution concepts compared throughout the mission: Gale's top trading cycles produce allocations with both properties, and the example of Section 7 shows that the first does not imply the second.
--
--   **Formalization Note** The paper defines an allocation as a zero-one matrix with column sums one and blocking by arbitrary $S$-allocations. Restricting to permutations loses nothing: a coalition all of whose members are strictly better off gives each member at least one item (owning nothing is ranked below everything), so it gives each exactly one, which is an $S$-permutation; and an allocation leaving some trader empty-handed is blocked by that trader alone. The blocking condition is strict for **every** member, as on p. 107 ("better for all its members"). The paper gives no displayed definition of competitive prices; the budget and optimization clauses above transcribe the argument of p. 114 ("can sell his own item for $\pi^j$ dollars", "cannot afford", "his utility is maximized") and the description on p. 105 ("individual optimization decisions will lead to a balance of supply and demand"). Prices are arbitrary reals; positivity is not part of the notion.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974); pp. 106-107 of the source printing, Section 2 (allocations, S-permutations, core allocation); p. 105, Section 1 and p. 114, Section 6 (competitive prices)

import Mathlib

namespace ShapleyScarf.TopTrading

/-- **Core allocation** (Shapley–Scarf 1974, §2, p. 107), for the housing market with traders `N`
and preference matrix `A` (`A i j` = trader `i`'s ordinal value of item `j`, the good brought by
trader `j`; ties allowed). The allocation gives trader `i` the item `σ i`; it is a permutation
allocation (`σ` bijective), and no nonempty coalition `S` has an `S`-permutation `τ` (a map
sending `S` injectively into `S`, i.e. a reshuffling of the items of `S` among the members of
`S`) that makes **every** member of `S` strictly better off. -/
def IsCoreAllocation {N : Type*} (A : N → N → ℝ) (σ : N → N) : Prop :=
  Function.Bijective σ ∧
    ¬ ∃ (S : Finset N) (τ : N → N), S.Nonempty ∧ (∀ i ∈ S, τ i ∈ S) ∧
        Set.InjOn τ (S : Set N) ∧ ∀ i ∈ S, A i (σ i) < A i (τ i)

/-- **Competitive allocation** (Shapley–Scarf 1974, §1 p. 105 and §6 p. 114). The permutation
allocation `σ` is competitive at the price vector `price` (`price k` = price of item `k`) if every
trader `i`, selling his own item for `price i`, can afford the item `σ i` he receives
(`price (σ i) ≤ price i`) and no affordable item is better for him than `σ i`. Supply equals
demand because `σ` is a bijection. -/
def IsCompetitive {N : Type*} (A : N → N → ℝ) (σ : N → N) (price : N → ℝ) : Prop :=
  Function.Bijective σ ∧
    ∀ i, price (σ i) ≤ price i ∧ ∀ k, price k ≤ price i → A i k ≤ A i (σ i)

end ShapleyScarf.TopTrading


