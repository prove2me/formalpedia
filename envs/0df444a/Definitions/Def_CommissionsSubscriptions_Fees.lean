-- Prove2me | Definitions.Def_CommissionsSubscriptions_Fees
-- name    : CommissionsSubscriptions_Fees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:24:05.825135+00:00
-- url     : https://prove2.me/theorems/0e13614b-f801-431d-934e-2debe84732be
-- title:
--   Commission-subscription pair $(\gamma,\mu)$
-- statement:
--   A **commission-subscription pair** $(\gamma,\mu)$ assigns to each seller type $i$ a commission rate $\gamma^s_i$ and a subscription fee $\mu^s_i$, and to each buyer type $j$ a commission rate $\gamma^b_j$ and a subscription fee $\mu^b_j$. When a type-$j$ buyer buys from a type-$i$ seller at price $p$, the buyer pays $p(1+\gamma^b_j)$ and the seller receives $p(1-\gamma^s_i)$; in addition each pays its subscription fee to the platform.
--
--   **Formalization Note** All real values are allowed in the structure; the feasible set $\Gamma\times\mathcal U$ is the predicate `InGammaU`.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), §2, p. 8

import Mathlib

namespace CommissionsSubscriptions

/-- **A commission-subscription pair `(γ, µ)`.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), §2, p. 8.

`gs i = γ^s_i` and `gb j = γ^b_j` are the commission rates charged to type-`i` sellers and type-`j`
buyers; `ms i = µ^s_i` and `mb j = µ^b_j` are the subscription fees. A type-`j` buyer who buys from
a type-`i` seller at price `p` pays `p(1 + γ^b_j) + µ^b_j`, and the seller receives
`p(1 − γ^s_i) − µ^s_i`.

**Formalization Note.** Any real values are allowed here; membership in `Γ × U` is `InGammaU`. -/
structure Fees (S B : Type) where
  /-- Seller commission rates `γ^s`. -/
  gs : S → ℝ
  /-- Buyer commission rates `γ^b`. -/
  gb : B → ℝ
  /-- Seller subscription fees `µ^s`. -/
  ms : S → ℝ
  /-- Buyer subscription fees `µ^b`. -/
  mb : B → ℝ

end CommissionsSubscriptions


