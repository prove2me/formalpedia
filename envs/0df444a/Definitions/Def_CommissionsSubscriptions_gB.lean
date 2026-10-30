-- Prove2me | Definitions.Def_CommissionsSubscriptions_gB
-- name    : CommissionsSubscriptions_gB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:29:38.826434+00:00
-- url     : https://prove2.me/theorems/2f64f21b-8068-42e5-8bbc-5851ac41d436
-- title:
--   Buyer term $g_j(q)=F^{-1}_{b_j}(1-q/b_j)\,q$
-- statement:
--   For a buyer type $j$ and $q\in[0,b_j]$,
--   $$g_j(q)=F^{-1}_{b_j}\Bigl(1-\frac{q}{b_j}\Bigr)\,q,$$
--   the revenue that $q$ units of type-$j$ demand generate when each buyer pays the marginal buyer's value. It is the buyer term of $h$ in (6) and of the objective (7a). By footnote 4, $g_j(0)=0$ also when the support is unbounded.
--
--   **Formalization Note** Real-valued. For $q\in(0,b_j]$ the argument of $F^{-1}$ is below $1$, so the value is finite; at $q=0$ the definition gives $0$. Only $q\in[0,b_j]$ is used.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), (6) and (7a), p. 12; footnote 4, p. 12; Lemma EC.1(ii), p. ec4

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Market
import Definitions.Def_CommissionsSubscriptions_Finv

namespace CommissionsSubscriptions

/-- **Buyer term of (6)/(7a): `g_j(q) = F⁻¹_{b_j}(1 − q/b_j) q`.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), (6) and (7a), p. 12; footnote 4, p. 12; Lemma EC.1(ii),
p. ec4.

**Formalization Note (Reading 1).** Real-valued. For `q ∈ (0, b_j]` the argument `1 − q/b_j` is
`< 1`, so `F⁻¹_{b_j}(1 − q/b_j)` is finite under Assumption 1 and `toReal` is exact. At `q = 0`
the value is `0 · toReal(F⁻¹(1)) = 0`, which is footnote 4's convention `F⁻¹_{b_j}(1)·0 = 0` for
`v̄_{b_j} = ∞` (and the true value `0 · v̄` when `v̄` is finite). Only `q ∈ [0, b_j]` is used. -/
noncomputable def gB {S B : Type} (M : Market S B) (j : B) (q : ℝ) : ℝ :=
  q * (Finv (M.Fb j) (1 - q / M.b j)).toReal

end CommissionsSubscriptions


