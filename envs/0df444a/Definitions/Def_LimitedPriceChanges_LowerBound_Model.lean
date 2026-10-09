-- Prove2me | Definitions.Def_LimitedPriceChanges_LowerBound_Model
-- name    : LimitedPriceChanges_LowerBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:40.907223+00:00
-- url     : https://prove2.me/theorems/4a3fd6fc-9146-4d11-aef6-440df09372fc
-- title:
--   Bernoulli pricing instance and clairvoyant revenue
-- statement:
--   In the lower-bound instance, demand in one period is Bernoulli with success probability
--   $$\nu(p,z)=\max\{0,1-pz/2\}.$$
--   The price lies in $[1,6]$, the parameter in $[1/6,5/6]$, the order-up-to level is one, and holding and lost-sale costs are zero. Expected revenue is $r_z(p)=p\nu(p,z)$. The optimal revenue is $G^*(z)=1/(2z)$, attained at $p=1/z$.
--
--   These functions isolate the dynamic-pricing instance used to establish the lower bound. **Formalization Note** The explicit benchmark is proved to be the maximum on the stated price interval in the local sanity file. The probability can be zero at a price beyond the kink; this is the paper's own instance.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), pp. 35–36, proof of Theorem 2

import Mathlib

namespace LimitedPriceChanges.LowerBound

/-- Bernoulli success probability in the instance of p. 35. -/
noncomputable def nu (p z : ℝ) : ℝ := max 0 (1 - p * z / 2)

/-- Revenue with order-up-to level one and zero holding and shortage costs. -/
noncomputable def rev (p z : ℝ) : ℝ := p * nu p z

/-- The optimal expected revenue on prices in [1,6], for z in [1/6,5/6]. -/
noncomputable def Gstar (z : ℝ) : ℝ := 1 / (2 * z)

end LimitedPriceChanges.LowerBound


