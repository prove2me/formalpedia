-- Prove2me | Definitions.Def_ProductFraming_Pricing_MNL
-- name    : ProductFraming_Pricing_MNL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:52.669098+00:00
-- url     : https://prove2.me/theorems/9f554d05-4be6-4bb1-b10b-92d200838d07
-- title:
--   MNL choice probabilities with linear price utilities and the revenue $R(r\mid S)$
-- statement:
--   This file defines the multinomial logit (MNL) choice model with price-dependent utilities and the expected revenue it induces from a single consumer.
--
--   There are $n$ products, indexed by $i \in [n]$. Product $i$ has a price-independent **quality** $a_i \in \mathbb R$ and a **price** $r_i \in \mathbb R$; $\beta$ is the **price sensitivity**. The mean utility of product $i$ is $u_i = a_i - \beta r_i$, and the outside alternative (no purchase) has utility $u_0 = 0$. A consumer whose consideration set is $S \subseteq [n]$ buys product $i$ with probability
--   $$
--   P(i,S) = \begin{cases} \dfrac{e^{u_i}}{1+\sum_{k\in S} e^{u_k}}, & i \in S,\\[2mm] 0, & \text{otherwise.}\end{cases}
--   $$
--   The expected revenue from a consumer with consideration set $S$ under the price vector $r=(r_1,\dots,r_n)$ is
--   $$
--   R(r\mid S) = \sum_{i\in S} r_i\,P(i,S).
--   $$
--
--   These two objects are the per-consumer ingredients of the joint pricing-and-framing problem: the total expected revenue averages $R(r\mid S)$ over the random consideration sets produced by a framing.
--
--   **Formalization Note.** Qualities and prices are functions `Fin n → ℝ`; $P(i,S)$ is `mnl a β r S i` and $R(r\mid S)$ is `revenue a β r S`. Prices are finite reals: the paper's priced-out products ($r_i = +\infty$) are modelled as products that are not displayed. The assumption $\beta>0$ is not part of the definition; every theorem that uses it states it as a hypothesis.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, §7, p. 15 (MNL choice model, u_i = a_i − βr_i, u_0 = 0) and §7.1, p. 16 (R(r|S))

import Mathlib
open Finset

namespace ProductFraming.Pricing

/-- MNL choice probability with price-dependent mean utilities (§7, p. 15):
`u_i = a_i - β r_i`, outside alternative `u_0 = 0`, and
`P(i,S) = e^{u_i} / (1 + ∑_{k∈S} e^{u_k})` for `i ∈ S`, `P(i,S) = 0` otherwise. -/
noncomputable def mnl {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ)
    (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ S then
    Real.exp (a i - β * r i) / (1 + ∑ k ∈ S, Real.exp (a k - β * r k))
  else 0

/-- Expected revenue from a consumer with ProductFraming.Nest.consideration set `S` under the price vector `r`
(§7.1, p. 16): `R(r|S) = ∑_{i∈S} r_i P(i,S)`. -/
noncomputable def revenue {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (r : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, r i * mnl a β r S i

end ProductFraming.Pricing


