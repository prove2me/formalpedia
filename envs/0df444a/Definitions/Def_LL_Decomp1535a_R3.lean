-- Prove2me | Definitions.Def_LL_Decomp1535a_R3
-- name    : LL_Decomp1535a_R3
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-30T14:07:48.569073+00:00
-- url     : https://prove2.me/theorems/79e3858a-50d1-4dbc-ae76-2912e61c57ce
-- title:
--   Weighted ternary prime count
-- statement:
--   For a natural number $N$, $R_3(N)=\sum \log p \log q \log r$ as a real number, summed over all triples of natural numbers $p,q,r \in [0,N]$ that are all prime and satisfy $p+q+r=N$.

import Mathlib

namespace LL_Decomp1535a

noncomputable section

open MeasureTheory

noncomputable def R3 (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N + 1),
    if p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = N then
      Real.log p * Real.log q * Real.log r else 0

end

end LL_Decomp1535a


