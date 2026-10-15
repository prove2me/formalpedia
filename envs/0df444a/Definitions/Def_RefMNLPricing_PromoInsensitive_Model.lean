-- Prove2me | Definitions.Def_RefMNLPricing_PromoInsensitive_Model
-- name    : RefMNLPricing_PromoInsensitive_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:29.645279+00:00
-- url     : https://prove2.me/theorems/689f61df-94e4-4ce4-97f2-4292632efd72
-- title:
--   §2.4, pp. 10–11 — the standing price-ceiling assumption p_H ≥ p̂_H, with p̂_H the solution of (9)
-- statement:
--   This module states the standing price-ceiling assumption of §2.4 of Guo, Jiang and Shen for the multi-product dynamic pricing model with reference effects under multinomial logit demand. The model itself (utility (2), shares (3), revenue (4), the box $\mathcal P^n=[0,p_H]^n$, the reference path (1), the discounted revenue, the optimal value $V^\star$ and the optimal steady state of Definition 4) is defined in the shared modules `RefMNLPricing.Myopic.Model`, `RefMNLPricing.Gap.Model` and `RefMNLPricing.GainSeeking.Model`, which this module imports.
--
--   There are $n$ products with parameters $a_i$, $b_i>0$ and $c_i^+,c_i^-\ge0$. With
--   $$\chi=\max_{i\in N}\frac{1}{b_i+\min\{c_i^+,c_i^-\}},$$
--   the right-hand side of (9) is
--   $$\chi+\sum_{i\in N}\frac{1}{b_i+c_i^+}\exp\big(a_i-b_ip+(b_i+c_i^+)\chi-1\big),$$
--   and the ceiling assumption says that some solution $\hat p_H$ of $p=$ (this right-hand side) satisfies $\hat p_H\le p_H$. By Proposition 1.2 the solution is unique, so this is the paper's "$p_H\ge\hat p_H$". Under it the myopic policy is unconstrained on $\mathcal P^n$; every theorem of the mission assumes it.
--
--   **Formalization Note** Products are indexed by `Fin n` (0-based). $\chi$ is a supremum over `Fin n`, which is $0$ when $n=0$. Uniqueness of the root of (9) is not assumed in the definition. The predicate coincides with the shared `RefMNLPricing.Myopic.CeilingOK`.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 10, (9); p. 11, §2.4 standing assumption

import Mathlib
import Definitions.Def_RefMNLPricing_GainSeeking_Model
import Definitions.Def_RefMNLPricing_Gap_Model
import Definitions.Def_RefMNLPricing_Myopic_Model

namespace RefMNLPricing.PromoInsensitive

/-- The standing ceiling assumption of §2.4, p. 11: `p_H ≥ p̂_H`, where `p̂_H` solves (9). -/
def CeilingOK {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ) : Prop :=
  ∃ pHat : ℝ, pHat = RefMNLPricing.Myopic.ceilRHS a b cp cm pHat ∧ pHat ≤ pH

end RefMNLPricing.PromoInsensitive


