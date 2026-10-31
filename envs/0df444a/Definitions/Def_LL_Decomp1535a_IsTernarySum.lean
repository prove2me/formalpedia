-- Prove2me | Definitions.Def_LL_Decomp1535a_IsTernarySum
-- name    : LL_Decomp1535a_IsTernarySum
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-30T14:07:33.935427+00:00
-- url     : https://prove2.me/theorems/f39dd119-bc92-41ec-9b28-6df89ee255f0
-- title:
--   Sum of three primes
-- statement:
--   A natural number $n$ is a sum of three primes if there exist primes $p, q, r$ with $p+q+r=n$.

import Mathlib

namespace LL_Decomp1535a

noncomputable section

def IsTernarySum (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n

end

end LL_Decomp1535a


