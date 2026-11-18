-- Prove2me | Definitions.Def_LL_Decomp587l_ZeroBelowOne
-- name    : LL_Decomp587l_ZeroBelowOne
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-18T01:24:07.751206+00:00
-- url     : https://prove2.me/theorems/a55dfac0-84d9-4560-a705-39d83afd396a
-- title:
--   Zero extension below one
-- statement:
--   For $\omega:\mathbb R\to\mathbb R$, the proposition that $\omega(u)=0$ for every real $u<1$.

import Mathlib

open Real Set

namespace LL_Decomp587l

def ZeroBelowOne (ω : ℝ → ℝ) : Prop := ∀ u : ℝ, u < 1 → ω u = 0

end LL_Decomp587l


