-- Prove2me | Definitions.Def_CommissionsSubscriptions_hS
-- name    : CommissionsSubscriptions_hS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:30:44.236451+00:00
-- url     : https://prove2.me/theorems/8f25f043-c6fd-4a70-a34b-ddc4126d3f72
-- title:
--   Seller term $h_i(q)=F^{-1}_{s_i}(q/s_i)\,q$ in $\overline{\mathbb R}$
-- statement:
--   For a seller type $i$ and $q\in[0,s_i]$,
--   $$h_i(q)=F^{-1}_{s_i}\Bigl(\frac{q}{s_i}\Bigr)\,q\ \in\mathbb R\cup\{+\infty\},$$
--   with $h_i(s_i)=\bar v_{s_i}s_i=+\infty$ when the support is unbounded. It is the seller term of $h$ in (6) and of the objective (7a).
--
--   **Formalization Note** Valued in the extended reals; $h_i(0)=F^{-1}(0)\cdot0=0$.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), (6) and (7a), p. 12

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Market
import Definitions.Def_CommissionsSubscriptions_Finv

namespace CommissionsSubscriptions

/-- **Seller term of (6)/(7a) in `EReal`: `h_i(q) = F⁻¹_{s_i}(q/s_i) q`.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), (6) and (7a), p. 12.

**Formalization Note (Reading 1).** `EReal`-valued, so that `h_i(s_i) = F⁻¹_{s_i}(1) s_i = ⊤`
when `v̄_{s_i} = ∞` (the paper's `h_i : [0, s_i] → ℝ ∪ {∞}`, p. ec2). At `q = 0` the value is
`F⁻¹(0) · 0 = 0`. -/
noncomputable def hS {S B : Type} (M : Market S B) (i : S) (q : ℝ) : EReal :=
  Finv (M.Fs i) (q / M.s i) * (q : EReal)

end CommissionsSubscriptions


