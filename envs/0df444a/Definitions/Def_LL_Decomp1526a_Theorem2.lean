-- Prove2me | Definitions.Def_LL_Decomp1526a_Theorem2
-- name    : LL_Decomp1526a_Theorem2
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-30T14:08:26.432116+00:00
-- url     : https://prove2.me/theorems/d12ca8e0-0a56-47c6-aa15-d71e79a90108
-- title:
--   Ramaré's Theorem 2 statement
-- statement:
--   The proposition that for every real $X\ge e^{67}$, the real number $X/5$ is at most the number of even natural numbers $N$ with $\lfloor X\rfloor<N\le\lfloor 2X\rfloor$ that are sums of two primes.

import Mathlib
import Definitions.Def_LL_Decomp1526a_IsGoldbachSum

namespace LL_Decomp1526a

noncomputable section

open Finset Real
open scoped Classical

def Theorem2 : Prop :=
  ∀ X : ℝ, exp 67 ≤ X →
    X / 5 ≤ (#{N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | Even N ∧ IsGoldbachSum N} : ℝ)

end

end LL_Decomp1526a


