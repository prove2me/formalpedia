-- Prove2me | Definitions.Def_RevenueOrdered_Ratio_Model
-- name    : RevenueOrdered_Ratio_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:05:29.872065+00:00
-- url     : https://prove2.me/theorems/c21b5eba-7452-47da-93f2-ee5f81884275
-- title:
--   §2, pp. 5–6 — regular discrete choice models, the revenue of an assortment and OPT
-- statement:
--   A firm sells a finite set $\mathcal C$ of products. Faced with a **choice set** $S\subseteq\mathcal C$, a consumer buys at most one product of $S$ or buys nothing. Write $\mathcal P(x,S)$ for the probability that the consumer buys product $x\in\mathcal C$ when offered $S$, and let $0$ denote the **no-purchase option**, with probability
--   $$
--   \mathcal P(0,S)=1-\sum_{x\in S}\mathcal P(x,S).
--   $$
--   The system of choice probabilities $\mathcal P$ is a **regular discrete choice model** if it satisfies the four axioms
--
--   1. $\mathcal P(x,S)\ge 0$ for every $x\in\mathcal C\cup\{0\}$ and $S\subseteq\mathcal C$;
--   2. $\mathcal P(x,S)=0$ for every $x\in\mathcal C$ and $S\subseteq\mathcal C\setminus\{x\}$;
--   3. $\sum_{x\in S}\mathcal P(x,S)\le 1$ for every $S\subseteq\mathcal C$;
--   4. (regularity) $\mathcal P(x,S)\ge\mathcal P(x,S')$ for every $S\subseteq S'\subseteq\mathcal C$ and every $x\in S\cup\{0\}$.
--
--   Axiom 4 covers the no-purchase option as well as the products: enlarging the choice set never makes the consumer more likely to leave without buying.
--
--   Given a revenue function $r:\mathcal C\to\mathbb R_{>0}$, the seller's **revenue** from offering $S$ is
--   $$
--   \operatorname{rev}(S)=\sum_{x\in S}\mathcal P(x,S)\,r(x),
--   $$
--   and $\mathrm{OPT}=\max_{S\subseteq\mathcal C}\operatorname{rev}(S)$ is the optimum of the **assortment problem**; the empty set is allowed and earns $0$.
--
--   These objects are the input of every result of the paper on revenue-ordered assortments.
--
--   **Formalization Note** The products form a finite type `C`, and `P : C → Finset C → ℝ` is defined on every pair; the no-purchase option is not an element of `C` but the derived quantity `noPurchase P S`. The structure `IsRegular` has six fields: axiom (i) is split into the product case and the no-purchase case (the latter also follows from (iii) and is kept to mirror the page), and axiom (iv) into the product case `mono` and the no-purchase case `noPurchase_mono`. Positivity of `r` is not part of these definitions; every theorem assumes it. `opt` is the maximum (`Finset.sup'`) of `revenue P r` over all finite subsets.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, pp. 5–6, §2, axioms (i)–(iv) and Definition 1

import Mathlib

namespace RevenueOrdered.Ratio

/-- The no-purchase probability `𝒫(0, S) := 1 − ∑_{x ∈ S} 𝒫(x, S)` (Berbeglia–Joret,
arXiv:1606.01371v3, §2, p. 5). The no-purchase option `0` is not a product: it is not an
element of `C`, and its probability is this derived quantity. -/
def noPurchase {C : Type*} (P : C → Finset C → ℝ) (S : Finset C) : ℝ :=
  1 - ∑ x ∈ S, P x S

/-- A regular discrete choice model (§2, p. 6). `P x S = 𝒫(x, S)` is the probability that a
consumer offered the choice set `S ⊆ 𝒞` buys product `x`. The fields are the paper's axioms:
* (i) `𝒫(x, S) ≥ 0` for products `x` (`nonneg`) and for the no-purchase option `x = 0`
  (`noPurchase_nonneg`; this case also follows from (iii));
* (ii) `𝒫(x, S) = 0` whenever `x ∉ S`;
* (iii) `∑_{x ∈ S} 𝒫(x, S) ≤ 1`;
* (iv) `𝒫(x, S) ≥ 𝒫(x, S')` for `S ⊆ S'` and `x ∈ S ∪ {0}`: the product case `mono` and the
  no-purchase case `noPurchase_mono`. -/
structure IsRegular {C : Type*} (P : C → Finset C → ℝ) : Prop where
  nonneg : ∀ (x : C) (S : Finset C), 0 ≤ P x S
  noPurchase_nonneg : ∀ S : Finset C, 0 ≤ noPurchase P S
  eq_zero_of_not_mem : ∀ (x : C) (S : Finset C), x ∉ S → P x S = 0
  sum_le_one : ∀ S : Finset C, ∑ x ∈ S, P x S ≤ 1
  mono : ∀ (S S' : Finset C) (x : C), S ⊆ S' → x ∈ S → P x S' ≤ P x S
  noPurchase_mono : ∀ S S' : Finset C, S ⊆ S' → noPurchase P S' ≤ noPurchase P S

/-- The seller's revenue `∑_{x ∈ S} 𝒫(x, S) r(x)` when offering the set `S`
(Definition 1, p. 6). -/
def revenue {C : Type*} (P : C → Finset C → ℝ) (r : C → ℝ) (S : Finset C) : ℝ :=
  ∑ x ∈ S, P x S * r x

/-- `OPT`, the maximum revenue over all subsets `S ⊆ 𝒞` (Definition 1, p. 6); the empty set
is allowed. -/
noncomputable def opt {C : Type*} [Fintype C] (P : C → Finset C → ℝ) (r : C → ℝ) : ℝ :=
  (Finset.univ : Finset (Finset C)).sup' Finset.univ_nonempty (revenue P r)

end RevenueOrdered.Ratio


