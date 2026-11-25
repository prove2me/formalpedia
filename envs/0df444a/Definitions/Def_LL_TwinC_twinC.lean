-- Prove2me | Definitions.Def_LL_TwinC_twinC
-- name    : LL_TwinC_twinC
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-25T04:01:10.794018+00:00
-- url     : https://prove2.me/theorems/82441e67-935b-4a57-8ca8-a8e4943a6ac3
-- title:
--   The twin prime constant $\prod_{p>2}(1-1/(p-1)^2)$
-- statement:
--   The real number $\prod_{p>2}\bigl(1-1/(p-1)^2\bigr)$, the unconditional product tprod over the primes $p>2$.

import Mathlib

namespace LL_TwinC

noncomputable section

def twinC : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)

end

end LL_TwinC


