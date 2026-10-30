-- Prove2me | Definitions.Def_HuangYin_demand
-- name    : HuangYin_demand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:36:01.763024+00:00
-- url     : https://prove2.me/theorems/271547c8-7d07-4502-a490-ee689d769da8
-- title:
--   Fraction of customers who buy, for one anecdote
-- statement:
--   Suppose each customer's single anecdote reveals product $H$ with probability $q$ and product $L$ with probability $1-q$. The fraction of the unit mass of customers who buy at price $p$ is
--
--   $$\gamma(p,q) = (1-q)\,\mathbf 1\{\text{an }L\text{-anecdote customer buys at }p\} + q\,\mathbf 1\{\text{an }H\text{-anecdote customer buys at }p\},$$
--
--   with both indicators given by the purchase rule (1). Hence $\gamma(p,q)=1$ for $p\le v_L$, $\gamma(p,q)=q$ for $v_L<p\le v_{HL}$ and $\gamma(p,q)=0$ for $p>v_{HL}$: these are the purchasing fractions $\gamma_1,\gamma_2$ of the paper's Lemma 1 for $K=1$.
--
--   **Formalization Note** The fraction is derived from rule (1), not copied from Lemma 1.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), Lemma 1, p. 10 (K = 1), derived from equation (1), p. 9

import Mathlib
import Definitions.Def_HuangYin_Buys

namespace HuangYin

/-- **The purchasing fraction for one anecdote** (Lemma 1 with `K = 1`, p. 10; derived from (1)).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), Lemma 1, p. 10 (the fractions γ1, γ2 for `K = 1`), derived from equation (1), p. 9.

`demand P p q` is the fraction of the unit mass of customers who buy at price `p` when each
customer's single anecdote reveals product `H` with probability `q` (and `L` with probability
`1 − q`): the customers with an `L`-anecdote buy iff `Buys P p false`, those with an
`H`-anecdote iff `Buys P p true`.

**Formalization Note.** The fraction is derived from the purchase rule (1), not copied from
Lemma 1's formulas. It gives `1` at `p = vL`, `q` at `p = vHL` and `0` above `vHL`, i.e. the γ's
of Lemma 1 for `K = 1`. -/
noncomputable def demand (P : Params) (p q : ℝ) : ℝ :=
  (1 - q) * (if Buys P p false then 1 else 0) + q * (if Buys P p true then 1 else 0)

end HuangYin


