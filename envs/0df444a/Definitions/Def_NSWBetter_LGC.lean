-- Prove2me | Definitions.Def_NSWBetter_LGC
-- name    : NSWBetter_LGC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:00:30.6992+00:00
-- url     : https://prove2.me/theorems/0ffb30e0-df83-4d52-8aaa-5d24e615dd6e
-- title:
--   Large good consistency property
-- statement:
--   $x$ satisfies the **large good consistency property** if
--   $$\sum_{g\in G_{nwb}}\sum_{i\in N_{wb}}\mathbb 1\{g\in L_i\}x_{ig}\le10\gamma n .$$
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 5, p.28 (Large Good Consistency Property)

import Mathlib
import Definitions.Def_NSWBetter_gamma
import Definitions.Def_NSWBetter_largeSet
import Definitions.Def_NSWBetter_Nwb
import Definitions.Def_NSWBetter_Gwb

namespace NSWBetter

open Classical in
/-- **Large good consistency.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 5, p.28: "the large good consistency property is satisfied if Σ_(g∈Gnwb) Σ_(i∈Nwb) 1{g ∈ Li} xig ≤ 10γn." -/
def LGC {n m : ℕ} (v : Fin n → Fin m → ℝ) (x : Fin n → Fin m → ℝ) : Prop :=
  ∑ g ∈ Finset.univ \ Gwb v x, ∑ i ∈ Nwb v x, (if g ∈ largeSet v x i then x i g else 0) ≤
    10 * gamma * n

end NSWBetter


