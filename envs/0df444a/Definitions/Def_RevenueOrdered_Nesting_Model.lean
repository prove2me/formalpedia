-- Prove2me | Definitions.Def_RevenueOrdered_Nesting_Model
-- name    : RevenueOrdered_Nesting_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:52:07.364977+00:00
-- url     : https://prove2.me/theorems/dccbbfa1-878e-46ea-83c1-ace1d546a9d1
-- title:
--   §2, pp. 5–6 — discrete choice axioms (i)–(iii) and regular discrete choice models
-- statement:
--   A firm sells a finite set $\mathcal C$ of products. Faced with a **choice set** $S\subseteq\mathcal C$, a consumer buys at most one product of $S$ or buys nothing. Write $\mathcal P(x,S)$ for the probability that the consumer buys product $x\in\mathcal C$ when offered $S$, and let $0$ denote the **no-purchase option**, with probability
--   $$
--   \mathcal P(0,S)=1-\sum_{x\in S}\mathcal P(x,S).
--   $$
--   The paper's four axioms on the system of choice probabilities $\mathcal P$ are
--
--   1. $\mathcal P(x,S)\ge 0$ for every $x\in\mathcal C\cup\{0\}$ and $S\subseteq\mathcal C$;
--   2. $\mathcal P(x,S)=0$ for every $x\in\mathcal C$ and $S\subseteq\mathcal C\setminus\{x\}$;
--   3. $\sum_{x\in S}\mathcal P(x,S)\le 1$ for every $S\subseteq\mathcal C$;
--   4. (regularity) $\mathcal P(x,S)\ge\mathcal P(x,S')$ for every $S\subseteq S'\subseteq\mathcal C$ and every $x\in S\cup\{0\}$.
--
--   Axioms 1–3 hold for every discrete choice model. A model satisfying all four is a **regular discrete choice model**. Axiom 4 covers the no-purchase option as well as the products: enlarging the choice set never makes the consumer more likely to leave without buying.
--
--   The regular model is the standing assumption of the multi-period analysis of §5; a few results of that analysis, which the paper attributes to Talluri and van Ryzin, need only axioms 1–3, so both notions are defined.
--
--   **Formalization Note** The products form a type `C`, and `P : C → Finset C → ℝ` is defined on every pair; the no-purchase option is not an element of `C` but the derived quantity `noPurchase P S`. `IsChoiceSystem P` collects axioms (i)–(iii), with axiom (i) split into the product case and the no-purchase case (the latter also follows from (iii) and is kept to mirror the page). `IsRegular P` extends it with axiom (iv), split into the product case `mono` and the no-purchase case `noPurchase_mono`.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, pp. 5–6, §2, axioms (i)–(iv)

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model

namespace RevenueOrdered.Nesting

/-- Axioms (i)–(iii) of a discrete choice model (§2, p. 6), which the paper notes "are satisfied
by any discrete choice model". `P x S = 𝒫(x, S)` is the probability that a consumer offered the
choice set `S ⊆ 𝒞` buys product `x`.
* (i) `𝒫(x, S) ≥ 0` for products `x` (`nonneg`) and for the no-purchase option `x = 0`
  (`noPurchase_nonneg`; this case also follows from (iii));
* (ii) `𝒫(x, S) = 0` whenever `x ∉ S`;
* (iii) `∑_{x ∈ S} 𝒫(x, S) ≤ 1`. -/
structure IsChoiceSystem {C : Type*} (P : C → Finset C → ℝ) : Prop where
  nonneg : ∀ (x : C) (S : Finset C), 0 ≤ P x S
  noPurchase_nonneg : ∀ S : Finset C, 0 ≤ RevenueOrdered.Ratio.noPurchase P S
  eq_zero_of_not_mem : ∀ (x : C) (S : Finset C), x ∉ S → P x S = 0
  sum_le_one : ∀ S : Finset C, ∑ x ∈ S, P x S ≤ 1

/-- A regular discrete choice model (§2, p. 6): axioms (i)–(iii) together with the regularity
axiom (iv), `𝒫(x, S) ≥ 𝒫(x, S')` for `S ⊆ S'` and `x ∈ S ∪ {0}`, split into the product case
`mono` and the no-purchase case `noPurchase_mono`. -/
structure IsRegular {C : Type*} (P : C → Finset C → ℝ) : Prop extends IsChoiceSystem P where
  mono : ∀ (S S' : Finset C) (x : C), S ⊆ S' → x ∈ S → P x S' ≤ P x S
  noPurchase_mono : ∀ S S' : Finset C, S ⊆ S' → RevenueOrdered.Ratio.noPurchase P S' ≤ RevenueOrdered.Ratio.noPurchase P S

end RevenueOrdered.Nesting


