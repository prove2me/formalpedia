-- Prove2me | Definitions.Def_LL_Decomp1535a_TernaryAbove
-- name    : LL_Decomp1535a_TernaryAbove
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-30T14:09:19.283997+00:00
-- url     : https://prove2.me/theorems/73df8ae0-8e91-4ada-a910-6bf13d901213
-- title:
--   Ternary statement above $C$
-- statement:
--   For a real $C$, the statement that every odd natural number $n$ with $C \le n$ is a sum of three primes.

import Mathlib
import Definitions.Def_LL_Decomp1535a_IsTernarySum

namespace LL_Decomp1535a

noncomputable section

def TernaryAbove (C : ℝ) : Prop := ∀ n : ℕ, Odd n → C ≤ n → IsTernarySum n

end

end LL_Decomp1535a


