-- Prove2me | Definitions.Def_CommissionsSubscriptions_hR
-- name    : CommissionsSubscriptions_hR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:30:13.753884+00:00
-- url     : https://prove2.me/theorems/f18cbd00-95b7-43eb-9969-fafaa65cf0f5
-- title:
--   Seller term $h_i(q)=F^{-1}_{s_i}(q/s_i)\,q$, real-valued
-- statement:
--   For a seller type $i$ and $q\in[0,s_i)$,
--   $$h_i(q)=F^{-1}_{s_i}\Bigl(\frac{q}{s_i}\Bigr)\,q,$$
--   the payment needed to attract $q$ units of type-$i$ supply when each seller receives the marginal seller's value. This real-valued version is used for the derivatives of $h_i$ on $(0,s_i)$, their one-sided limits, and continuity.
--
--   **Formalization Note** Exact on $[0,s_i)$, and at $s_i$ when the support is bounded. When $\bar v_{s_i}=\infty$ the paper's $h_i(s_i)=+\infty$, which this real function does not represent; the extended-valued $h_i$ is `hS`.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), (7a), p. 12; Lemma EC.1(ii), p. ec4

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Market
import Definitions.Def_CommissionsSubscriptions_Finv

namespace CommissionsSubscriptions

/-- **Seller term of (7a) as a real function: `h_i(q) = F⁻¹_{s_i}(q/s_i) q` on `[0, s_i)`.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), (7a), p. 12; Lemma EC.1(ii), p. ec4.

**Formalization Note (Reading 1).** Exact on `[0, s_i)`, where `q/s_i < 1` and `F⁻¹_{s_i}` is
finite; also exact at `q = s_i` when the support is bounded. When `v̄_{s_i} = ∞` the paper's
`h_i(s_i) = ∞`, while `toReal ⊤ = 0`; so this function is used only for derivatives on
`(0, s_i)` and their one-sided limits (footnote 22), never for the value at `s_i`. The
extended-valued `h_i` used in the objective of (7) is `hS`. -/
noncomputable def hR {S B : Type} (M : Market S B) (i : S) (q : ℝ) : ℝ :=
  q * (Finv (M.Fs i) (q / M.s i)).toReal

end CommissionsSubscriptions


