-- Prove2me | Definitions.Def_SecondBestMatch_IsBIC
-- name    : SecondBestMatch_IsBIC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:42.647336+00:00
-- url     : https://prove2.me/theorems/ee5e6f19-4773-4b35-b2d4-82aeb8d2f298
-- title:
--   Bayesian incentive compatibility on the full report domain
-- statement:
--   With interim utilities $u_i(v;z) = v\,x_i(z) - p_i(z)$ for buyers and $u_j(c;z) = r_j(z) - c\,y_j(z)$ for sellers, a mechanism is **Bayesian incentive compatible (BIC) on the full report domain** if for every buyer $i$, every seller $j$ and all $v,z,c,w\in[0,1]$,
--   $$
--   u_i(v;v)\ge u_i(v;z),\qquad u_j(c;c)\ge u_j(c;w).
--   $$
--   Reports of probability zero under the prior are included.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Definition 2.1, p.8

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_interimBuyerService
import Definitions.Def_SecondBestMatch_interimSellerService
import Definitions.Def_SecondBestMatch_interimPay
import Definitions.Def_SecondBestMatch_interimRecv

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- Bayesian incentive compatibility on the full report domain (Definition 2.1, Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), p.8): for
every buyer `i` and all `v, z ∈ [0, 1]`, `uᵢ(v; v) ≥ uᵢ(v; z)` with `uᵢ(v; z) = v xᵢ(z) − pᵢ(z)`;
for every seller `j` and all `c, w ∈ [0, 1]`, `uⱼ(c; c) ≥ uⱼ(c; w)` with
`uⱼ(c; w) = rⱼ(w) − c yⱼ(w)`. -/
def IsBIC {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (A : Mechanism B S) : Prop :=
  (∀ i, ∀ v ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) 1,
    v * interimBuyerService m A.alloc i z - interimPay m A i z ≤
      v * interimBuyerService m A.alloc i v - interimPay m A i v) ∧
  (∀ j, ∀ c ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (0 : ℝ) 1,
    interimRecv m A j w - c * interimSellerService m A.alloc j w ≤
      interimRecv m A j c - c * interimSellerService m A.alloc j c)

end SecondBestMatch


