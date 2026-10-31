-- Prove2me | Definitions.Def_LL_Decomp1526a_IsGoldbachSum
-- name    : LL_Decomp1526a_IsGoldbachSum
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-30T14:07:59.231898+00:00
-- url     : https://prove2.me/theorems/821f7329-a16e-40dd-90e5-7490c4ddba96
-- title:
--   Sum of two primes
-- statement:
--   A natural number $n$ is a Goldbach sum if there exist primes $p$ and $q$ with $p+q=n$.

import Mathlib

namespace LL_Decomp1526a

noncomputable section

def IsGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

end

end LL_Decomp1526a


