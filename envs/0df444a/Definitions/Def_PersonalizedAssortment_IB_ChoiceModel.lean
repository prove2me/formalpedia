-- Prove2me | Definitions.Def_PersonalizedAssortment_IB_ChoiceModel
-- name    : PersonalizedAssortment_IB_ChoiceModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T01:29:10.857996+00:00
-- url     : https://prove2.me/theorems/1f252bb6-f38b-4658-a94b-f95c220ce089
-- title:
--   General choice model $\varphi_i(S)$ and Assumption 1 (substitutability)
-- statement:
--   A firm sells $n$ products, indexed here by $\{0,1,\dots,n-1\}$ (the paper uses $1,\dots,n$). An **assortment** is a set $S$ of products. A **general choice model** gives, for every assortment $S$ and every product $i$, the probability $\varphi_i(S)$ that a customer buys product $i$ when offered $S$. It satisfies
--
--   1. $\varphi_i(S) \ge 0$;
--   2. $\varphi_i(S) = 0$ whenever $i \notin S$;
--   3. $\sum_{i\in S}\varphi_i(S) \le 1$.
--
--   The remaining mass $1-\sum_{i\in S}\varphi_i(S)$ is the probability that the customer buys nothing (the paper's product $0$). Each customer buys at most one product. Every customer type $z$ in a set $\mathcal Z$ carries its own choice model $\varphi^z$.
--
--   Let $\mathcal S$ be a family of **feasible assortments**. The family of choice models satisfies **Assumption 1 (Substitutability)** when, for every type $z\in\mathcal Z$, every $S\in\mathcal S$ and all products $i\ne j$,
--   $$\varphi_i^z(S)\;\ge\;\varphi_i^z(S\cup\{j\}).$$
--   In words, adding a product to a feasible assortment never raises the purchase probability of another product. Every random-utility model satisfies this condition, including the multinomial and nested logit.
--
--   These are the demand primitives of the online assortment problem. Every other statement of the mission is phrased in terms of them.
--
--   **Formalization Note** The choice model is defined on every subset of products, not only on feasible ones, because Assumption 1 evaluates it at $S\cup\{j\}$, which need not lie in $\mathcal S$. Only the single-purchase model is formalized. The paper mentions a multi-purchase generalization $\Phi^z(S',S)$ but states that it uses only $\varphi_i^z$ from then on.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1536, Section 2 (choice model); p. 1537, Assumption 1

import Mathlib

namespace PersonalizedAssortment.IB

/-- A general (single-purchase) choice model on products `Fin n` (Golrezaei, Nazerzadeh and
Rusmevichientong 2014, §2, p. 1536). `prob S i` is `φ_i(S)`, the probability that the customer
buys product `i` when the assortment `S` is offered. It is defined on every assortment (not only
on the feasible ones), because Assumption 1 evaluates it at `S ∪ {j}`. The no-purchase option
(product 0 of the paper) has probability `1 - ∑_{i ∈ S} φ_i(S)`. -/
structure ChoiceModel (n : ℕ) where
  /-- `prob S i = φ_i(S)`. -/
  prob : Finset (Fin n) → Fin n → ℝ
  /-- Purchase probabilities are nonnegative. -/
  prob_nonneg : ∀ S i, 0 ≤ prob S i
  /-- A product that is not offered is never bought. -/
  prob_eq_zero_of_not_mem : ∀ S i, i ∉ S → prob S i = 0
  /-- The purchase probabilities of the offered products sum to at most one. -/
  sum_prob_le_one : ∀ S, ∑ i ∈ S, prob S i ≤ 1

/-- Assumption 1 (Substitutability), p. 1537: for every customer type `z`, every feasible
assortment `S ∈ 𝒮` and all products `i ≠ j`, `φ_i^z(S) ≥ φ_i^z(S ∪ {j})`. -/
def Substitutable {n : ℕ} {Z : Type*} (𝒮 : Finset (Finset (Fin n))) (φ : Z → ChoiceModel n) :
    Prop :=
  ∀ z : Z, ∀ S ∈ 𝒮, ∀ i j : Fin n, i ≠ j → (φ z).prob (insert j S) i ≤ (φ z).prob S i

end PersonalizedAssortment.IB


