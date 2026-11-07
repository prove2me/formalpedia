-- Prove2me | Definitions.Def_NSWBetter_tailSum
-- name    : NSWBetter_tailSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:12.703879+00:00
-- url     : https://prove2.me/theorems/608b129d-89b6-42e2-a244-0e7c39f41e9a
-- title:
--   Total value of the goods after the first $\ell$
-- statement:
--   $\mathrm{tail}(s,\ell)=\sum_{k>\ell}v(g_k)$: the total value of the goods other than the $\ell$ most valuable ones. When $L=\{g_1,\dots,g_\ell\}$ it is $v(G\setminus L)$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 3.2, p.11 ($v(G\setminus L)$)

import Mathlib
import Definitions.Def_NSWBetter_sortDesc

namespace NSWBetter

/-- **Value of all but the ℓ most valuable goods.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 3.2, p.11: `v(G \ L)`.

`tailSum s ℓ = v(g_(ℓ+1)) + … + v(g_m)`, the sum of the sorted values from position `ℓ` on.

**Formalization Note.** An instance with identical valuations is given by its number of agents `Δ` and the multiset `s` of the values of its goods; every notion of Section 3 depends only on these (round-robin bundle values do not depend on how ties are broken, p.23). -/
noncomputable def tailSum (s : Multiset ℝ) (ℓ : ℕ) : ℝ := ((sortDesc s).drop ℓ).sum

end NSWBetter


